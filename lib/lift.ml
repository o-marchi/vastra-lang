(* @: each (await x) is pulled out of the expression around it, in
   evaluation order, into a chain of tasks, up to its boundary: a function's
   body, a branch of an if or a match clause, or else the top-level form.
   (:count @model) becomes
   (task/and-then <the task for model> (fn [@1] (task/succeed (:count @1)))). *)

open Ast

let count = ref 0

(* "@1" cannot clash with a name in the program: the reader reads @ as await. *)
let fresh () =
  incr count;
  "@" ^ string_of_int !count

(* Nodes made here say they come from @, so errors in them name it. *)
let at (e : expr) kind = { kind; span = e.span; origin = Some "@"; typed = Untyped }
let var e name = at e (Var name)
let call e f args = at e (Call { func = var e f; args })
let succeed e = call e "task/succeed" [ e ]

let chain binds tail =
  List.fold_right
    (fun (name, task) rest ->
      call task "task/and-then"
        [ task; at task (Fn { params = [ name_at name task.span ]; body = rest }) ])
    binds tail

(* [e] with its awaits replaced by names, and the tasks giving those names, in
   the order they run. *)
let rec anf (e : expr) =
  let rebuild kind = { e with kind } in
  match e.kind with
  | Await x ->
      let binds, x = anf x in
      let name = fresh () in
      (binds @ [ (name, at e (Task_of x)) ], var e name)
  | Int _ | Hex _ | Float _ | Bool _ | Str _ | Var _ | Keyword _ | Quote _ | Quasi _ | Task_of _
  | Run _ ->
      ([], e)
  | Vector items ->
      let binds, items = each items in
      (binds, rebuild (Vector items))
  | Record fields ->
      let binds, values = each (List.map snd fields) in
      (binds, rebuild (Record (List.combine (List.map fst fields) values)))
  | Get g ->
      let binds, record = anf g.record in
      (binds, rebuild (Get { g with record }))
  | Read { target; path } ->
      let b1, target = anf target in
      let b2, path = steps path in
      (b1 @ b2, rebuild (Read { target; path }))
  | Set { target; path; value } ->
      let b1, target = anf target in
      let b2, path = steps path in
      let b3, value = anf value in
      (b1 @ b2 @ b3, rebuild (Set { target; path; value }))
  | Update { target; path; func } ->
      let b1, target = anf target in
      let b2, path = steps path in
      let b3, func = anf func in
      (b1 @ b2 @ b3, rebuild (Update { target; path; func }))
  | Change { target; value } ->
      let binds, value = anf value in
      (binds, rebuild (Change { target; value }))
  | Send x ->
      let binds, x = anf x in
      (binds, rebuild (Send x))
  | Call { func; args } ->
      let binds, parts = each (func :: args) in
      (binds, rebuild (Call { func = List.hd parts; args = List.tl parts }))
  | Fn l -> ([], rebuild (Fn { l with body = fst (lifted l.body) }))
  (* Branches are boundaries: if one awaits, the others become tasks too, and
     the if or match is a task, awaited where it is. *)
  | If { condition; then_branch; else_branch } ->
      let binds, condition = anf condition in
      let t = lifted then_branch in
      let f = lifted else_branch in
      let task = snd t || snd f in
      awaited e binds task
        (If { condition; then_branch = branch task t; else_branch = branch task f })
  | Match { scrutinee; clauses } ->
      let binds, scrutinee = anf scrutinee in
      let bodies = Util.map_in_order (fun (_, body) -> lifted body) clauses in
      let task = List.exists snd bodies in
      awaited e binds task
        (Match
           { scrutinee; clauses = List.map2 (fun (p, _) b -> (p, branch task b)) clauses bodies })
  | Let { bindings; body; how } -> let_ e how bindings body
  | Par_let { bindings; body } ->
      let value (b, v) =
        match anf v with
        | [], v -> (b, v)
        | (_, waits) :: _, _ ->
            Diagnostic.fail
              (Diagnostic.make ~why:"parallel" Syntax waits.span
                 "a binding of par/let cannot wait for a task: the bindings run together"
              |> Diagnostic.note "wait for it in a let around the par/let")
      in
      let bindings = Util.map_in_order value bindings in
      let body, task = lifted body in
      awaited e [] task (Par_let { bindings; body })

and each es =
  let results = Util.map_in_order anf es in
  (List.concat_map fst results, List.map snd results)

and steps path =
  let results =
    Util.map_in_order
      (function
        | At x ->
            let binds, x = anf x in
            (binds, At x)
        | key -> ([], key))
      path
  in
  (List.concat_map fst results, List.map snd results)

(* [e] as it runs: unchanged if it awaits nothing, else a task giving its value. *)
and lifted e =
  match anf e with
  | [], e -> (e, false)
  | [ (name, task) ], { kind = Var v; _ } when v = name -> (task, true)
  | binds, value -> (chain binds (succeed value), true)

and branch task (body, awaits) = if task && not awaits then succeed body else body

and awaited e binds task kind =
  if task then
    let name = fresh () in
    (binds @ [ (name, { e with kind }) ], var e name)
  else (binds, { e with kind })

(* A binding's awaits run after the bindings before it, which they may use. *)
and let_ e how bindings body =
  let rec split before = function
    | [] -> (List.rev before, None)
    | (b, v) :: rest -> (
        match anf v with
        | [], v -> split ((b, v) :: before) rest
        | binds, v -> (List.rev before, Some (binds, (b, v) :: rest)))
  in
  let keep before inner =
    if before = [] then inner
    else { e with kind = Let { bindings = before; body = inner; how } }
  in
  match split [] bindings with
  | before, None -> (
      match lifted body with
      | body, false -> ([], { e with kind = Let { bindings = before; body; how } })
      | body, true ->
          let name = fresh () in
          ([ (name, keep before body) ], var e name))
  | before, Some (binds, rest) ->
      let inner, task = lifted { e with kind = Let { bindings = rest; body; how } } in
      let inner = if task then inner else succeed inner in
      let name = fresh () in
      ([ (name, keep before (chain binds inner)) ], var e name)

(* At the top level a definition's tasks run when it is defined (Run); an
   expression that awaits is a task, which the REPL or a program runs. *)
(* The first @ in [e] that isn't inside a function value. *)
let rec first_await (e : expr) =
  match e.kind with
  | Await _ -> Some e
  | Fn _ -> None
  | _ -> List.find_map first_await (children e)

let top : top -> top = function
  | Def d -> (
      match lifted d.value with
      | value, false -> Def { d with value }
      | task, true -> Def { d with value = at task (Run task) })
  | Expr e -> Expr (fst (lifted e))
  | On o -> On { o with handler = fst (lifted o.handler) }
  (* A view only reads: it runs after every change. *)
  | View ({ place; draw = { kind = Fn l; _ }; _ } as v) -> (
      let refuse (at : expr) message =
        Diagnostic.fail (Diagnostic.make ~why:"views" Syntax at.span message)
      in
      Option.iter
        (fun at -> refuse at "a view's place is a selector or a window, which needs no @")
        (first_await place);
      match first_await l.body with
      | Some at ->
          Diagnostic.fail
            (Diagnostic.make ~why:"views" Syntax at.span "a view cannot wait"
            |> Diagnostic.note
                 "it is drawn after every change, and a wait would hold up the drawing")
      | None -> View v)
  | top -> top
