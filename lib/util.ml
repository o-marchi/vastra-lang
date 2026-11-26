(* List.map with a guaranteed left-to-right order, so the first error raised is the leftmost. *)
let map_in_order f items =
  let rec go acc = function
    | [] -> List.rev acc
    | x :: rest ->
        let y = f x in
        go (y :: acc) rest
  in
  go [] items

(* The shortest text that reads back as the same float. *)
let float_to_string f =
  if Float.is_nan f then "NaN"
  else if Float.is_integer f && Float.abs f < 1e15 then Printf.sprintf "%.1f" f
  else if f = Float.infinity then "Infinity"
  else if f = Float.neg_infinity then "-Infinity"
  else
    List.find
      (fun s -> float_of_string s = f)
      [ Printf.sprintf "%.15g" f; Printf.sprintf "%.16g" f; Printf.sprintf "%.17g" f ]

let contains text part =
  let n = String.length part in
  let rec at i =
    i + n <= String.length text && (String.sub text i n = part || at (i + 1))
  in
  at 0

(* A map's key that ends in ? may be missing, and reads as an Option. *)
let may_miss key = String.ends_with ~suffix:"?" key
