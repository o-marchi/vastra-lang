(* Used once: a name holding a buffer is used once on each path through
   the code, so set and update can change the buffer in place and no one sees
   the old value. Reads may come before that use: a read finishes before
   anything changes. A function cannot hold a buffer from outside, and its
   type says which parameters it only reads. Checked after inference, on the
   types it found. *)

open Ast
module Ids = Map.Make (Int)

(* Whether a value of a type holds a buffer: never, maybe (a generic type, or
   (vector a), a vector or a buffer), or surely. *)
type held = Never | Generic | Either | Surely

(* What inference found. [line]: the line of a byte of the source. *)
type found = {
  binding : binding -> Types.t; (* a parameter's or a let's *)
  pattern : pattern -> Types.t; (* a pattern variable's *)
  got : expr -> Types.t; (* what a get gives, what a vector holds *)
  held : Types.t -> held;
  no_buffer : Types.t -> string -> unit; (* a type holds no buffer, and why *)
  reads : string -> int list; (* the parameters a global function only reads *)
  shown : string -> string; (* a global name as typed here *)
  line : int -> int;
}

(* What uses a name from outside it: a function, or a par/let binding, which
   runs with the others. Each makes its own buffers. *)
type part = Function | Binding

(* [name], holding a buffer, used in a [part] from outside it; [origin]: the
   macro that made the function, if one did. *)
let from_outside ?(part = Function) name span origin =
  let cannot =
    match part with
    | Function -> "a function cannot hold"
    | Binding -> "a par/let binding cannot use"
  in
  let d =
    Diagnostic.make ~why:"buffer-held" Type span
      (Printf.sprintf "%s `%s` from outside, since it holds a buffer" cannot name)
  in
  Diagnostic.fail
    (Option.fold origin ~none:d ~some:(fun m ->
         Diagnostic.note (Printf.sprintf "in this use of `%s`" m) d))

(* A name in scope: one that holds no buffer, one that may (an id), one from
   outside the part being checked, or a local function, with the parameters
   it only reads. *)
type entry = Plain | Held of int | Outside of int * part | Local of int list

(* [scope] seen from inside a [part]. *)
let outside part scope =
  List.map
    (fun (name, entry) ->
      (name, match entry with Held id | Outside (id, _) -> Outside (id, part) | e -> e))
    scope

(* The parameters the function [e] only reads; [self] is its own name, if it
   can call itself. *)
let check found ?self (e : expr) =
  let types = Hashtbl.create 16 in
  let bind (scope, st) name ty =
    if found.held ty = Never then ((name, Plain) :: scope, st)
    else
      let id = Hashtbl.length types in
      Hashtbl.add types id ty;
      ((name, Held id) :: scope, Ids.add id None st)
  in
  (* [name] used up [by] someone, or only read. The state gives each id what
     used it up, and where, once something has. What maybe holds a buffer
     holds none once used twice. *)
  let use scope st name (span : Reader.span) ~by ~origin =
    match List.assoc_opt name scope with
    | Some (Held id) when found.held (Hashtbl.find types id) <> Never -> (
        let ty = Hashtbl.find types id in
        match (Ids.find id st, by) with
        | Some (who, (first : Reader.span)), _ ->
            if found.held ty = Surely then
              Diagnostic.fail
                (Diagnostic.make Type span
                   (Printf.sprintf "`%s` is a buffer, and %s used it up before this" name
                      who)
                |> Diagnostic.mark first "used up here"
                |> Diagnostic.why "buffer-used-up"
                |> Diagnostic.note
                     "a buffer changes in place, so one place holds it: buffer/freeze \
                      makes a vector to share");
            found.no_buffer ty
              (Printf.sprintf "`%s` is used twice, at line %d, so it cannot be a buffer"
                 name (found.line span.start));
            st
        | None, Some who -> Ids.add id (Some (who, span)) st
        | None, None -> st)
    | Some (Outside (id, part)) ->
        let ty = Hashtbl.find types id in
        if found.held ty = Surely then from_outside ~part name span origin;
        let does = match part with Function -> "holds" | Binding -> "uses" in
        found.no_buffer ty
          (Printf.sprintf "a %s %s `%s` from outside, at line %d, so it cannot be a buffer"
             (if part = Function then "function" else "par/let binding")
             does name (found.line span.start));
        st
    | _ -> st
  in
  (* Each branch from the same state; after them, a buffer is used up if one
     branch used it. *)
  let either = function
    | first :: rest ->
        let first_use _ a b = Some (if a = None then b else a) in
        List.fold_left (Ids.union first_use) first rest
    | [] -> invalid_arg "either"
  in
  let rec vars acc (p : pattern) =
    match p.pat with
    | PVar x -> bind acc x (found.pattern p)
    | PCtor (_, ps) | PVector ps -> List.fold_left vars acc ps
    | _ -> acc
  in
  (* [who] gets the value of [e]; [origin]: the macro that made the function
     being checked, if one did. *)
  let rec walk ~origin scope st who (e : expr) =
    let walk' = walk ~origin scope and together' = together ~origin scope in
    match e.kind with
    | Var x -> use scope st x e.span ~by:(Some who) ~origin
    | Int _ | Hex _ | Float _ | Bool _ | Str _ | Keyword _ | Quote _ -> st
    | Vector items -> (
        let st = together' st "a vector" items in
        let why = "a vector cannot hold a buffer" in
        match found.held (found.got e) with
        | Surely ->
            let at = match items with i :: _ -> i.span | [] -> e.span in
            Diagnostic.fail (Diagnostic.make ~why:"buffer-held" Type at why)
        | Never -> st
        | _ ->
            found.no_buffer (found.got e) why;
            st)
    | Record fields -> together' st "a map" (List.map snd fields)
    | Get { record = { kind = Var n; _ }; _ } when Analyze.joined n -> st
    | Get { key; record } -> together' st ("`:" ^ key ^ "`") [ record ]
    | Read { target; path } ->
        let by = if found.held (found.got e) = Never then None else Some "`get`" in
        changed ~origin scope st target path [] by
    | Set { target; path; value } ->
        changed ~origin scope st target path [ value ] (Some "`set`")
    | Update { target; path; func } ->
        changed ~origin scope st target path [ func ] (Some "`update`")
    | Change { value; _ } -> walk' st "`set!`" value
    | Send x -> walk' st "`send!`" x
    | Fn l ->
        ignore (lambda scope e l);
        st
    | Par_let { bindings; body } ->
        let part = outside Binding scope in
        let scope, st =
          List.fold_left
            (fun acc ((b : binding), v) ->
              bind (fst acc, walk ~origin part (snd acc) "`par/let`" v) b.name
                (found.binding b))
            (scope, st) bindings
        in
        walk ~origin scope st who body
    | Let { bindings; body; how } ->
        let scope, st =
          List.fold_left
            (fun (scope, st) ((b : binding), (v : expr)) ->
              match v.kind with
              | Fn l ->
                  let self = if how = Recursive then Some b.name else None in
                  ((b.name, Local (settle ?self scope v l)) :: scope, st)
              | _ ->
                  let st = walk ~origin scope st "`let`" v in
                  bind (scope, st) b.name (found.binding b))
            (scope, st) bindings
        in
        walk ~origin scope st who body
    | If { condition; then_branch; else_branch } ->
        let st = walk' st "`if`" condition in
        either [ walk' st who then_branch; walk' st who else_branch ]
    | Match { scrutinee; clauses } ->
        let st = walk' st "`match`" scrutinee in
        either
          (List.map
             (fun (p, body) ->
               let scope, st = vars (scope, st) p in
               walk ~origin scope st who body)
             clauses)
    | Call { func; args } ->
        let callee, reads =
          match func.kind with
          | Var f -> (
              ( "`" ^ found.shown f ^ "`",
                match List.assoc_opt f scope with
                | Some (Local reads) -> reads
                | Some _ -> []
                | None -> found.reads f ))
          | _ -> ("a call", [])
        in
        together ~origin ~reads scope (walk' st "a call" func) callee args
    | Quasi q ->
        let rec template st = function
          | Unquote x -> walk' st "`~`" x
          | Coll (_, items) ->
              List.fold_left
                (fun st -> function
                  | Item q -> template st q | Splice x -> walk' st "`~@`" x)
                st items
          | Leaf _ | Gensym _ -> st
        in
        template st q
    | Await x | Task_of x | Run x -> walk' st who x
  (* [es] given together to [who]: each in turn, then the names among them
     used up as [who] runs, so a read in a later one comes before. [who]
     only reads those at [reads]. *)
  and together ~origin ?(reads = []) scope st who es =
    let st =
      List.fold_left
        (fun st (e : expr) ->
          match e.kind with Var _ -> st | _ -> walk ~origin scope st who e)
        st es
    in
    List.fold_left
      (fun st (i, (e : expr)) ->
        match e.kind with
        | Var x ->
            let by = if List.mem i reads then None else Some who in
            use scope st x e.span ~by ~origin
        | _ -> st)
      st
      (List.mapi (fun i e -> (i, e)) es)
  (* get, set and update: the target, the path and the last argument,
     then the target is read, or used up [by] the change. *)
  and changed ~origin scope st (target : expr) path last by =
    let who = Option.value by ~default:"`get`" in
    let st = match target.kind with Var _ -> st | _ -> walk ~origin scope st who target in
    let st =
      List.fold_left
        (fun st -> function At i -> walk ~origin scope st who i | Key _ -> st)
        st path
    in
    let st = List.fold_left (fun st v -> walk ~origin scope st who v) st last in
    match target.kind with Var x -> use scope st x target.span ~by ~origin | _ -> st
  (* A function's body, from its parameters: what it holds from outside is
     outside. Gives the parameters it only reads, of those that may hold a
     buffer. *)
  and lambda scope (fn : expr) (l : lambda) =
    let scope, st =
      List.fold_left
        (fun acc (p : binding) -> bind acc p.name (found.binding p))
        (outside Function scope, Ids.empty) l.params
    in
    let st = walk ~origin:fn.origin scope st "`fn`" l.body in
    List.concat
      (List.mapi
         (fun i (p : binding) ->
           match List.assoc p.name scope with
           | Held id
             when Ids.find id st = None && found.held (Hashtbl.find types id) >= Either ->
               [ i ]
           | _ -> [])
         l.params)
  (* A function that calls itself reads what it reads, assuming its calls to
     itself read all they can: fewer and fewer, until that holds. *)
  and settle ?self scope fn l =
    let rec go assumed =
      let inner =
        Option.fold self ~none:scope ~some:(fun n -> (n, Local assumed) :: scope)
      in
      let reads = lambda inner fn l in
      if self = None || reads = assumed then reads else go reads
    in
    go (List.mapi (fun i _ -> i) l.params)
  in
  match e.kind with
  | Fn l -> settle ?self [] e l
  | Var f -> found.reads f
  | _ ->
      ignore (walk ~origin:None [] Ids.empty "`fn`" e);
      []
