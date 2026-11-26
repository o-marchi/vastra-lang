(* What is being typed: text over several lines with a cursor (a byte
   offset), and the history. *)

let next_char = Look.next_char

let prev_char s i =
  let rec go j = if j > 0 && Look.is_cont s.[j] then go (j - 1) else j in
  go (i - 1)

let chars s a b =
  let n = ref 0 in
  for i = a to b - 1 do
    if not (Look.is_cont s.[i]) then incr n
  done;
  !n

let line_start s i =
  match String.rindex_from_opt s (i - 1) '\n' with Some j -> j + 1 | None -> 0

let line_end s i = Option.value (String.index_from_opt s i '\n') ~default:(String.length s)

(* [k] characters after [i], without leaving its line. *)
let advance s i k =
  let e = line_end s i in
  let rec go i k = if k = 0 || i >= e then i else go (next_char s i) (k - 1) in
  go i k

type t = { mutable text : string; mutable pos : int }

let create () = { text = ""; pos = 0 }

let set t s =
  t.text <- s;
  t.pos <- String.length s

let replace t a b s =
  t.text <- String.sub t.text 0 a ^ s ^ String.sub t.text b (String.length t.text - b);
  t.pos <- a + String.length s

let insert t s = replace t t.pos t.pos s

(* The indentation of a new line at [pos], Clojure style: two spaces inside a
   form like fn or let, under the first argument of a call, one space inside
   [ or {. *)
let indent src pos =
  let cls = Syntax.classify src in
  let stack = ref [] in
  for i = 0 to pos - 1 do
    if cls.(i) = Bracket then
      if Syntax.opening src.[i] then stack := i :: !stack
      else stack := match !stack with _ :: rest -> rest | [] -> []
  done;
  match !stack with
  | [] -> 0
  | o :: _ ->
      let column i = chars src (line_start src i) i in
      let rec skip j p = if j < pos && p src.[j] then skip (j + 1) p else j in
      let h = skip (o + 1) (fun c -> not (Syntax.delimiter c)) in
      let a = skip h (( = ) ' ') in
      if src.[o] <> '(' then column o + 1
      else if List.mem (String.sub src (o + 1) (h - o - 1)) Syntax.block_forms then column o + 2
      else if h > o + 1 && a < pos && src.[a] <> '\n' then column a
      (* A cond's clauses go two spaces in when the first starts a line, as
         cljfmt lays them out. *)
      else if String.sub src (o + 1) (h - o - 1) = "cond" then column o + 2
      else column o + 1

(* Terminals send a pasted line's end as \r or \r\n. *)
let paste t s =
  let strip l = if String.ends_with ~suffix:"\r" l then String.sub l 0 (String.length l - 1) else l in
  insert t (String.map (fun c -> if c = '\r' then '\n' else c) (String.concat "\n" (List.map strip (String.split_on_char '\n' s))))

let newline t = insert t ("\n" ^ String.make (indent t.text t.pos) ' ')
let left t = if t.pos > 0 then t.pos <- prev_char t.text t.pos
let right t = if t.pos < String.length t.text then t.pos <- next_char t.text t.pos
let home t = t.pos <- line_start t.text t.pos
let end_ t = t.pos <- line_end t.text t.pos
let backspace t = if t.pos > 0 then replace t (prev_char t.text t.pos) t.pos ""
let delete t = if t.pos < String.length t.text then replace t t.pos (next_char t.text t.pos) ""
let kill_before t = replace t (line_start t.text t.pos) t.pos ""
let kill_after t = replace t t.pos (line_end t.text t.pos) ""

let kill_word t =
  let rec back j p = if j > 0 && p t.text.[j - 1] then back (j - 1) p else j in
  let j = back (back t.pos (( = ) ' ')) (fun c -> not (Syntax.delimiter c)) in
  replace t j t.pos ""

(* Up and down move between lines; false on the first or last. *)
let up t =
  let ls = line_start t.text t.pos in
  ls > 0
  && (t.pos <- advance t.text (line_start t.text (ls - 1)) (chars t.text ls t.pos);
      true)

let down t =
  let le = line_end t.text t.pos in
  le < String.length t.text
  && (t.pos <- advance t.text (le + 1) (chars t.text (line_start t.text t.pos) t.pos);
      true)

(* The history, newest first. Browsing goes through the entries [found] for
   what was [typed]: those starting with it, then those containing it. [at] is
   the entry shown, -1 when not browsing. *)
type history = {
  mutable entries : string list;
  mutable found : string list;
  mutable at : int;
  mutable typed : string;
}

let history entries = { entries; found = []; at = -1; typed = "" }

let remember h entry =
  h.entries <- List.filteri (fun i _ -> i < 1000) (entry :: List.filter (( <> ) entry) h.entries);
  h.at <- -1

let contains s sub = Term.find s sub <> None

let older h typed =
  if h.at < 0 then (
    h.typed <- typed;
    let starting = List.filter (String.starts_with ~prefix:typed) h.entries in
    h.found <- starting @ List.filter (fun e -> contains e typed && not (List.mem e starting)) h.entries);
  if h.at + 1 >= List.length h.found then None
  else (
    h.at <- h.at + 1;
    Some (List.nth h.found h.at))

let newer h =
  if h.at < 0 then None
  else (
    h.at <- h.at - 1;
    Some (if h.at < 0 then h.typed else List.nth h.found h.at))

(* The file: a header, then an entry per line, its newlines written \n and its
   backslashes \\. A file without the header is linenoise's: a line per entry. *)
let header = ";; vastra history"

let escape s =
  let b = Buffer.create (String.length s) in
  String.iter
    (function
      | '\n' -> Buffer.add_string b "\\n" | '\\' -> Buffer.add_string b "\\\\" | c -> Buffer.add_char b c)
    s;
  Buffer.contents b

let unescape s =
  let b = Buffer.create (String.length s) in
  let rec go i =
    if i < String.length s then
      if s.[i] = '\\' && i + 1 < String.length s then (
        Buffer.add_char b (if s.[i + 1] = 'n' then '\n' else s.[i + 1]);
        go (i + 2))
      else (
        Buffer.add_char b s.[i];
        go (i + 1))
  in
  go 0;
  Buffer.contents b

let load path =
  match In_channel.with_open_text path In_channel.input_lines with
  | first :: lines when first = header -> List.rev_map unescape lines
  | lines -> List.rev lines
  | exception Sys_error _ -> []

let save path entries =
  try
    Out_channel.with_open_text path (fun oc ->
        List.iter (fun e -> output_string oc (e ^ "\n")) (header :: List.rev_map escape entries))
  with Sys_error _ -> ()
