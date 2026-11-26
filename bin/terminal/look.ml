(* Rows of styled characters, and how they are written for the colours the
   terminal has. *)

type colour = int * int * int

type style = {
  fg : colour option;
  bg : colour option;
  bold : bool;
  italic : bool;
  reverse : bool;
  wavy : colour option; (* a wavy underline, in this colour *)
}

let plain = { fg = None; bg = None; bold = false; italic = false; reverse = false; wavy = None }
let fg c = { plain with fg = Some c }

(* A row has a cell per character; a cell with none paints the rest of the row
   with its background. *)
type cell = { ch : string; style : style }

let is_cont c = Char.code c land 0xC0 = 0x80

let next_char s i =
  let rec go j = if j < String.length s && is_cont s.[j] then go (j + 1) else j in
  go (i + 1)

let text style s =
  let rec go i acc =
    if i >= String.length s then List.rev acc
    else
      let j = next_char s i in
      go j ({ ch = String.sub s i (j - i); style } :: acc)
  in
  go 0 []

(* Cells split at their newlines. *)
let lines row =
  let rec go cur acc = function
    | [] -> List.rev (List.rev cur :: acc)
    | { ch = "\n"; _ } :: rest -> go [] (List.rev cur :: acc) rest
    | c :: rest -> go (c :: cur) acc rest
  in
  go [] [] row

let fill colour = { ch = ""; style = { plain with bg = Some colour } }
let width row = List.length (List.filter (fun c -> c.ch <> "") row)

let cut n row =
  if width row <= n then row
  else List.filteri (fun i _ -> i < n - 1) row @ text plain "…"

let rec chunks n row =
  if List.length row < n then [ row ]
  else List.filteri (fun i _ -> i < n) row :: chunks n (List.filteri (fun i _ -> i >= n) row)

type mode = Full | Colours256 | No_colour

let mode = ref Full

let mode_of_env () =
  match (Sys.getenv_opt "NO_COLOR", Sys.getenv_opt "COLORTERM") with
  | Some s, _ when s <> "" -> No_colour
  | _, Some ("truecolor" | "24bit") -> Full
  | _ -> Colours256

(* The nearest of xterm's 256 colours: in its 6×6×6 cube, or among its greys. *)
let nearest (r, g, b) =
  let steps = [| 0; 95; 135; 175; 215; 255 |] in
  let level v = if v < 48 then 0 else if v < 115 then 1 else (v - 35) / 40 in
  let lr = level r and lg = level g and lb = level b in
  let grey = max 0 (min 23 ((((r + g + b) / 3) - 3) / 10)) in
  let distance (x, y, z) = ((x - r) * (x - r)) + ((y - g) * (y - g)) + ((z - b) * (z - b)) in
  let v = 8 + (10 * grey) in
  if distance (steps.(lr), steps.(lg), steps.(lb)) <= distance (v, v, v) then
    16 + (36 * lr) + (6 * lg) + lb
  else 232 + grey

let colour code = function
  | Some (r, g, b) when !mode = Full -> [ Printf.sprintf "%d;2;%d;%d;%d" code r g b ]
  | Some c when !mode = Colours256 -> [ Printf.sprintf "%d;5;%d" code (nearest c) ]
  | _ -> []

let sgr s =
  let flags = [ (s.bold, "1"); (s.italic, "3"); (s.reverse, "7") ] in
  let codes =
    ("0" :: List.filter_map (fun (on, code) -> if on then Some code else None) flags)
    @ colour 38 s.fg @ colour 48 s.bg
  in
  let underline =
    match (s.wavy, !mode) with
    | None, _ -> ""
    | Some (r, g, b), Full -> Printf.sprintf "\027[4:3m\027[58:2::%d:%d:%dm" r g b
    | Some c, Colours256 -> Printf.sprintf "\027[4:3m\027[58:5:%dm" (nearest c)
    | Some _, No_colour -> "\027[4:3m"
  in
  "\027[" ^ String.concat ";" codes ^ "m" ^ underline

let render row =
  let b = Buffer.create 128 in
  let last = ref None in
  List.iter
    (fun c ->
      if !last <> Some c.style then (
        Buffer.add_string b (sgr c.style);
        last := Some c.style);
      Buffer.add_string b (match c.ch with "" -> "\027[K" | "\t" -> " " | ch -> ch))
    row;
  Buffer.add_string b "\027[0m";
  Buffer.contents b
