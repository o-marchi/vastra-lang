(* The mark, -(-)-, as a creature: the thread passes through the
   parentheses. In the banner it rests; on the status line its arms say what
   is going on. Every pose is five characters, so nothing beside it moves. *)

open Look

type pose = Resting | Waving | Weaving | Cheering | Spinning | Drooping | Asleep | Looking

let frames = function
  | Resting | Asleep -> [| "-(-)-" |]
  | Waving -> [| "-(-)/"; "-(-)-" |]
  | Weaving -> [| "\\(-)/"; "-(-)-"; "/(-)\\"; "-(-)-" |]
  | Cheering -> [| "\\(o)/"; "-(o)-" |]
  | Spinning -> [| "\\(-)\\"; "|(-)|"; "/(-)/"; "-(-)-" |]
  | Drooping -> [| "_(-)_" |]
  | Looking -> [| "-(o)-"; "-(-)-" |]

let moves pose = Array.length (frames pose) > 1

(* A frame each quarter of a second. *)
let cells pose now =
  let f = frames pose in
  let frame = f.(int_of_float (now /. 0.25) mod Array.length f) in
  let thread =
    match pose with
    | Drooping -> Theme.error ()
    | Asleep -> Theme.faint ()
    | _ -> Theme.thread ()
  in
  List.init 5 (fun i ->
      let ch = String.make 1 frame.[i] in
      { ch; style = fg (if ch = "(" || ch = ")" then Theme.ink () else thread) })
