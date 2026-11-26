(* Laying out values and types for a width, in the style of Wadler's
   pretty printer: a group goes on one line if it fits, or each of its items
   goes on a line of its own, aligned after the group's opening, as Clojure
   code is indented. *)

type t =
  | Text of string
  | Group of { opening : string; items : t list; sep : string; closing : string }

let rec flat = function
  | Text s -> s
  | Group g -> g.opening ^ String.concat g.sep (List.map flat g.items) ^ g.closing

(* In characters, not bytes. *)
let length s =
  String.fold_left (fun n c -> if Char.code c land 0xC0 = 0x80 then n else n + 1) 0 s

(* Without a width, one line. [col] is where the first line starts. *)
let render ?width ?(col = 0) doc =
  match width with
  | None -> flat doc
  | Some width ->
      let b = Buffer.create 80 in
      (* [trail]: what must follow on the same line, a closing or a comma. *)
      let rec go col trail = function
        | Group g as doc when col + length (flat doc) + trail > width ->
            Buffer.add_string b g.opening;
            let inner = col + length g.opening in
            let sep = String.trim g.sep in
            let rec items = function
              | [] -> inner
              | [ x ] -> go inner (trail + length g.closing) x
              | x :: rest ->
                  ignore (go inner (length sep) x);
                  Buffer.add_string b (sep ^ "\n" ^ String.make inner ' ');
                  items rest
            in
            let col = items g.items in
            Buffer.add_string b g.closing;
            col + length g.closing
        | doc ->
            let s = flat doc in
            Buffer.add_string b s;
            col + length s
      in
      ignore (go col 0 doc);
      Buffer.contents b
