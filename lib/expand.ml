(* Macro expansion, before analysis, so a macro's output is type-checked like
   hand-written code. Macros are Vastra functions (macro); [macro name]
   finds the one a name refers to. *)

open Reader

(* Forms holding types or quoted data rather than code, left as written. *)
let declarations = [ "type"; "native"; "quote"; "::" ]
let limit = 10_000

let rec expand ~macro (node : node) : node =
  let count = ref 0 in
  let rec outer (node : node) =
    match node.form with
    | List ({ form = Symbol name; _ } :: _ as items) -> (
        match macro name with
        | Some run ->
            incr count;
            if !count > limit then
              Diagnostic.fail
                (Diagnostic.make ~why:"quasiquote" Syntax node.span
                   (Printf.sprintf "the expansion of `%s` never stops" name));
            outer (run items node.span)
        | None -> node)
    | _ -> node
  in
  let node = outer node in
  let each = Util.map_in_order (expand ~macro) in
  match node.form with
  | List ({ form = Symbol head; _ } :: _) when List.mem head declarations -> node
  | List [ ({ form = Symbol "quasiquote"; _ } as q); template ] ->
      { node with form = List [ q; holes ~macro template ] }
  | List items -> { node with form = List (each items) }
  | Vector items -> { node with form = Vector (each items) }
  | Map entries ->
      let entry (k, v) =
        let k = expand ~macro k in
        (k, expand ~macro v)
      in
      { node with form = Map (Util.map_in_order entry entries) }
  | _ -> node

(* Inside a quasiquote, only the code in ~ and ~@ holes is expanded. *)
and holes ~macro (node : node) =
  match node.form with
  | List [ ({ form = Symbol ("unquote" | "unquote-splicing"); _ } as u); e ] ->
      { node with form = List [ u; expand ~macro e ] }
  | List items -> { node with form = List (List.map (holes ~macro) items) }
  | Vector items -> { node with form = Vector (List.map (holes ~macro) items) }
  | Map entries ->
      {
        node with
        form = Map (List.map (fun (k, v) -> (holes ~macro k, holes ~macro v)) entries);
      }
  | _ -> node
