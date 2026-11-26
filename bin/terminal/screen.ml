(* The window. What has happened is printed into the scrollback, from row
   [next] down; the live area is drawn on the bottom rows, with blank rows in
   between until the transcript reaches it. *)

let height = ref 24
let width = ref 80
let next = ref 0 (* the row the transcript's next line goes on *)
let live = ref 0 (* the live area's height, as last drawn *)
let drawn = ref None (* its rows, while the screen still shows them as drawn *)
let goto row = Printf.sprintf "\027[%d;1H" (row + 1)

(* A row fixed at the top, once [pin] has been called: the terminal scrolls
   only the rows under it. Some terminals then keep no scrollback; modern
   ones do. *)
let fixed = ref false
let pinned = ref None (* the top row, as last drawn *)
let first () = if !fixed then 1 else 0
let region () = Printf.sprintf "\027[2;%dr" !height

(* The window scrolls up [n] rows; the top ones go into the scrollback. *)
let scroll n =
  if n > 0 then (
    Term.emit (goto (!height - 1) ^ String.make n '\n');
    next := max (first ()) (!next - n))

(* False if the terminal does not say where its cursor is. *)
let start () =
  match (Term.position (), Term.size ()) with
  | Some (row, col), Some (h, w) ->
      next := if col = 0 then row else row + 1;
      height := h;
      width := w;
      true
  | _ -> false

let paint rows =
  let h = List.length rows in
  Term.emit ("\027[?2026h" ^ goto !next ^ "\027[J");
  scroll (!next + h - !height);
  let top = !height - h in
  Term.emit
    (goto top ^ String.concat "\r\n" (List.map (fun r -> Look.render (Look.cut (!width - 1) r)) rows));
  (* The terminal's cursor waits, hidden, on the live area's first row: after a
     resize, it tells where the live area went. *)
  Term.emit (goto top ^ "\027[?2026l");
  live := h;
  drawn := Some rows;
  Term.flush ()

(* Painting the same rows again would drop the terminal's selection in them. *)
let draw rows =
  let rows = List.filteri (fun i _ -> i >= List.length rows - !height) rows in
  if !drawn <> Some rows then paint rows

(* Rows printed above the live area; the next [draw] puts the live area back. *)
let print rows =
  drawn := None;
  Term.emit ("\027[?2026h" ^ goto !next ^ "\027[J");
  List.iter
    (fun r ->
      let n = max 1 ((Look.width r + !width - 1) / !width) in
      scroll (!next + n - (!height - !live));
      Term.emit (goto !next ^ Look.render r);
      next := !next + n)
    rows

(* The top row, drawn again only when it changed. The first time, what the
   window shows moves a row down to make room, scrolling first if it is full. *)
let pin row =
  if not !fixed then (
    if !next >= !height - 1 then scroll 1;
    Term.emit (goto 0 ^ "\027[L");
    next := !next + 1;
    fixed := true;
    Term.emit (region ());
    drawn := None);
  if !pinned <> Some row then (
    pinned := Some row;
    Term.emit
      ("\027[?2026h" ^ goto 0 ^ Look.render (Look.cut (!width - 1) row) ^ "\027[K"
     ^ goto (!height - !live) ^ "\027[?2026l");
    Term.flush ())

let resize () =
  drawn := None;
  let gap = !height - !live - !next in
  (match Term.position () with
  | Some (row, _) -> next := max (first ()) (row - gap)
  | None -> ());
  (match Term.size () with
  | Some (h, w) ->
      height := h;
      width := w
  | None -> ());
  if !fixed then (
    Term.emit (region ());
    pinned := None)

let clear () =
  drawn := None;
  Term.emit (goto !next ^ "\027[J");
  scroll (!next - first ())

let stop () =
  Term.emit ((if !fixed then "\027[r" else "") ^ goto !next ^ "\027[J");
  Term.flush ()
