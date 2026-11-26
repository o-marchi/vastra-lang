(* The live area's rows: [top] (a waiting line), the input on its strip,
   [below] (a menu, the keys), then the status line, whose parts are [status]
   (None to leave it out). [input w] gives the input's rows, at most [w] wide.
   [busy] dims the prompt. *)

open Look

let spaces n = text plain (String.make (max 0 n) ' ')

(* Code, results and messages start at the edge; the columns before it hold
   only the prompt and ✗. *)
let edge = 3
let indent = spaces edge

let prompted ?(busy = false) rows =
  let prompt = fg (if busy then Theme.faint () else Theme.thread ()) in
  List.mapi (fun i r -> text prompt (if i = 0 then " › " else "   ") @ r) rows

(* A row on [bg] to the right edge; cells keep their own background. *)
let under bg row =
  List.map (fun c -> if c.style.bg = None then { c with style = { c.style with bg = Some bg } } else c) row
  @ [ fill bg ]

let on_strip row = under (Theme.strip ()) row

let status_row w (left, right) =
  let left = if width left > w - edge - 1 - width right then cut (w - edge - 1 - width right) left else left in
  indent @ left @ spaces (max 1 (w - edge - width left - width right)) @ right

let rows ~width ~top ~input ~below ~status ~busy =
  let w = width - 1 in
  let blank = [ fill (Theme.strip ()) ] in
  top
  @ (blank :: List.map on_strip (prompted ~busy (input (w - edge))))
  @ (blank :: below)
  @ Option.to_list (Option.map (status_row w) status)

(* A menu: up to six items (a name, and what it is), the chosen one marked. *)
let menu_rows items sel =
  let first = max 0 (sel - 5) in
  let namew = List.fold_left (fun w (name, _) -> max w (Look.width (text plain name))) 0 items in
  let row k (name, detail) =
    let name = text plain name @ spaces (namew - Look.width (text plain name) + 2) in
    if first + k = sel then
      let name = List.map (fun c -> { c with style = Theme.bold (Theme.ink ()) }) name in
      under (Theme.selected ()) (text (fg (Theme.thread ())) " › " @ name @ detail)
    else indent @ List.map (fun c -> { c with style = fg (Theme.ink ()) }) name @ detail
  in
  let more = List.length items - first - 6 in
  List.mapi row (List.filteri (fun i _ -> i >= first && i < first + 6) items)
  @ if more > 0 then [ indent @ text (fg (Theme.muted ())) (Printf.sprintf "… %d more" more) ] else []
