(* A tree-walking interpreter for type-checked programs. Meeting a value of the
   wrong kind is a bug in the language, reported as an internal error.

   Global names are looked up when used (late binding), in [globals], by the
   key the session gave the code: the cell of the version of the name it was
   checked against. *)

open Value

(* [globals] are those of the closure running: a page can hold several sessions,
   and the browser calls back into any of them. *)
type t = { mutable depth : int; max_depth : int; mutable globals : Value.t ref Env.t ref }

let internal span message = Diagnostic.fail (Diagnostic.bug span message)

let global ev span key =
  match Env.find_opt key !(ev.globals) with
  | Some cell -> cell
  | None -> internal span ("unknown name " ^ key)

(* A local holds each number type the running generic function was told,
   under a name no program can write. The names are made once: [num] runs
   for every literal in generic code. *)
let told =
  let names = Dynarray.create () in
  fun v ->
    for i = Dynarray.length names to v do
      Dynarray.add_last names ("'" ^ string_of_int i)
    done;
    Dynarray.get names v

let num span locals : Ast.num -> Num.t = function
  | Known t -> t
  | Hidden v -> (
      match List.assoc_opt (told v) locals with
      | Some (Told t) -> t
      | _ -> internal span "a number type no one told")

(* The number types a generic name is used at. *)
let types (e : Ast.expr) locals =
  match e.typed with Use ns -> List.map (num e.span locals) ns | _ -> []

(* A function generic over number waits for the types it is used at. *)
let generic (fn : Ast.expr) locals closure =
  match fn.typed with
  | Generic vars ->
      Generic
        (fun types -> closure (List.map2 (fun v t -> (told v, Told t)) vars types @ locals))
  | _ -> closure locals

(* The bindings [p] makes when it matches [v], innermost first. *)
let rec matches (p : Ast.pattern) v binds =
  match (p.pat, v) with
  | PWild, _ -> Some binds
  | PVar name, _ -> Some ((name, v) :: binds)
  | PInt a, v -> if is_whole a v then Some binds else None
  | PStr a, Str b -> if a = b then Some binds else None
  | PBool a, Bool b -> if a = b then Some binds else None
  | PCtor (name, ps), Ctor (name', vs) when name = name' -> all ps vs binds
  | PVector ps, Vector vs when List.length ps = Array.length vs ->
      all ps (Array.to_list vs) binds
  | _ -> None

and all ps vs binds =
  List.fold_left2 (fun acc p v -> Option.bind acc (matches p v)) (Some binds) ps vs

let steps here =
  Util.map_in_order (function
    | Ast.Key (k, _) -> Value.Key k
    | Ast.At x -> Value.At (here x))

let field span key = function
  | Record fields -> ( try Value.field key fields with Internal m -> internal span m)
  | _ -> internal span "reading a key from a value that is not a map"

(* A closure's body scope: its captured locals, its own name, its arguments. *)
let scope f (c : closure) args =
  let s = match c.name with Some n -> (n, f) :: c.locals | None -> c.locals in
  List.fold_left2 (fun s (p : Ast.binding) a -> (p.name, a) :: s) s c.lambda.params args

(* Set by the REPL's terminal on Ctrl+C: the evaluation stops, and its
   submission is undone like a failed one. *)
let stop = Atomic.make false

(* The origin and text of the code running now: a runtime error's spans are
   in it, and a function from another file or submission brings its own. *)
let source : (string * string) option ref = ref None

let same a b =
  match (a, b) with Some (_, a), Some (_, b) -> a == b | None, None -> true | _ -> false

let stopped () =
  Diagnostic.fail
    (Diagnostic.make ~why:"stopped" Runtime Diagnostic.nowhere
       "the evaluation was stopped (Ctrl+C)"
    |> Diagnostic.note "nothing from this submission is kept")

(* Set by the session: what to do before a top-level task waits. *)
let waiting = ref ignore

(* Runs a top-level task. Natively the timers run until it ends, so the
   next line waits for it; a page can't wait here, and gives None for a task
   that ends later. Ctrl+C stops it. *)
let run_top run =
  let r = Value.running () and outcome = ref None in
  Value.within r (fun () -> run (fun o -> outcome := Some o));
  if !outcome = None && Clock.pending () then (
    !waiting ();
    Clock.run ~until:(fun () -> !outcome <> None || Atomic.get stop) ());
  if Atomic.get stop then (
    Value.stop r;
    stopped ());
  !outcome

(* A nested evaluation: counts towards the depth limit. Every call evaluates
   its function here, so a loop of tail calls also meets [stop]. *)
let rec eval ev (e : Ast.expr) locals =
  if Atomic.get stop then stopped ();
  if ev.depth >= ev.max_depth then
    Diagnostic.fail
      (Diagnostic.make ~why:"depth" Runtime e.span
         (Printf.sprintf "evaluation is nested too deeply (limit: %d)" ev.max_depth)
      |> Diagnostic.note "only calls in tail position can repeat without limit");
  ev.depth <- ev.depth + 1;
  (* No need to restore the depth on errors: an evaluator is dropped after one. *)
  let v = run ev e locals in
  ev.depth <- ev.depth - 1;
  v

(* Calls to [run] in tail position are OCaml tail calls: a tail call in Vastra
   continues here without growing the stack. *)
and run ev (e : Ast.expr) locals =
  let here x = eval ev x locals in
  match e.kind with
  | Int n | Hex n -> ( match e.typed with Literal t -> literal (num e.span locals t) n | _ -> Int n)
  | Float f -> Float f
  | Bool b -> Bool b
  | Str s -> Str s
  | Keyword k -> Keyword k
  | Var name -> (
      match (e.typed, List.assoc_opt name locals) with
      | Told_type shape, _ -> Json.told shape !(global ev e.span name)
      | _, Some (Generic g) -> g (types e locals)
      | _, Some v -> v
      | _, None -> (
          (* Stored, a global function still follows its redefinitions. *)
          let cell = global ev e.span name in
          match !cell with
          | Closure _ | Builtin _ | Generic _ -> Global (cell, types e locals)
          | v -> v))
  | Vector items -> Vector (Array.of_list (Util.map_in_order here items))
  | Record fields -> Record (Util.map_in_order (fun (k, v) -> (k, here v)) fields)
  | Get { key; record } -> field e.span key (here record)
  | Read { target; path } -> (
      let v = here target in
      let path = steps here path in
      try Value.get v path with Internal m -> internal e.span m)
  | Set { target; path; value } -> (
      let v = here target in
      let path = steps here path in
      try Value.change ~adds:true v path (fun _ -> here value)
      with Internal m -> internal e.span m)
  | Update { target; path; func } -> (
      let v = here target in
      let path = steps here path in
      let f = here func in
      try
        Value.change ~adds:false v path (function
          | Some old -> apply ev f [ old ] e.span
          | None -> internal e.span "update added a step")
      with Internal m -> internal e.span m)
  | Change { target = { kind = Var key; _ }; value } ->
      let v = here value in
      let cell = global ev e.span key in
      Option.iter (fun l -> Value.assigned := Some ((cell, !cell) :: l)) !Value.assigned;
      cell := v;
      !Value.changed cell;
      Unit
  | Change _ -> internal e.span "set! of what is not a name"
  | Send x ->
      Value.send (here x);
      Unit
  | Fn lambda ->
      let source = !source in
      generic e locals (fun locals ->
          Closure { name = None; lambda; locals; globals = ev.globals; source })
  | Await _ -> internal e.span "@ that Lift did not pull out"
  | Task_of x -> here x
  | Run x -> (
      match here x with
      | Task run -> (
          match run_top run with
          | Some (Ok v) -> v
          | Some (Error err) ->
              Diagnostic.fail (Diagnostic.untaken e.span (Value.to_string err))
          | None ->
              Diagnostic.fail
                (Diagnostic.make ~why:"task-failed" Runtime e.span
                   "a definition whose task finishes later (in a page) is not supported \
                    yet"))
      | _ -> internal e.span "running a definition's value that is not a task")
  (* The interpreter runs a par/let's bindings one at a time. *)
  | Let { bindings = [ (b, ({ kind = Fn lambda; _ } as fn)) ]; body; how = Recursive } ->
      let source = !source in
      let closure locals =
        Closure { name = Some b.name; lambda; locals; globals = ev.globals; source }
      in
      run ev body ((b.name, generic fn locals closure) :: locals)
  | Let { bindings; body; _ } | Par_let { bindings; body } ->
      let s =
        List.fold_left
          (fun s ((b : Ast.binding), v) -> (b.name, eval ev v s) :: s)
          locals bindings
      in
      run ev body s
  | If { condition; then_branch; else_branch } -> (
      match here condition with
      | Bool true -> run ev then_branch locals
      | Bool false -> run ev else_branch locals
      | _ -> internal condition.span "if condition is not a Bool")
  | Match { scrutinee; clauses } -> (
      let v = here scrutinee in
      let v = match e.typed with Decodes shape -> Json.decode shape v | _ -> v in
      match
        List.find_map
          (fun (p, body) -> Option.map (fun b -> (b, body)) (matches p v []))
          clauses
      with
      | Some (binds, body) -> run ev body (binds @ locals)
      | None -> internal e.span "no clause matched")
  | Quote n -> Form (at_site n)
  | Quasi q ->
      let fresh = Hashtbl.create 4 in
      let made form = made ~default:e.span form in
      let as_form = function
        | Form n -> n
        | _ -> internal e.span "~ of a value that is not a Form"
      in
      let rec template = function
        | Ast.Leaf n -> at_site n
        | Gensym base -> (
            match Hashtbl.find_opt fresh base with
            | Some n -> n
            | None ->
                incr gensyms;
                let n = made (Symbol (Printf.sprintf "%s__%d" base !gensyms)) in
                Hashtbl.add fresh base n;
                n)
        | Unquote x -> as_form (here x)
        | Coll (coll, items) ->
            let items =
              List.concat_map
                (function
                  | Ast.Item q -> [ template q ]
                  | Splice x -> (
                      match here x with
                      | Vector v -> List.map as_form (Array.to_list v)
                      | _ -> internal e.span "~@ of a value that is not a vector"))
                items
            in
            let rec pairs = function k :: v :: rest -> (k, v) :: pairs rest | _ -> [] in
            made
              (match coll with
              | CList -> List items
              | CVector -> Vector items
              | CMap -> Map (pairs items))
      in
      Form (template q)
  | Call { func; args } -> (
      let f = match here func with Global (cell, types) -> at !cell types | f -> f in
      let args = Util.map_in_order here args in
      match f with
      | Closure c when c.globals == ev.globals && same c.source !source ->
          run ev c.lambda.body (scope f c args)
      | _ -> apply ev f args e.span)

and apply ev f args span =
  match f with
  | Global (cell, types) -> apply ev (at !cell types) args span
  | Closure c ->
      let globals = ev.globals and here = !source in
      ev.globals <- c.globals;
      source := c.source;
      let v = eval ev c.lambda.body (scope f c args) in
      ev.globals <- globals;
      source := here;
      v
  | Builtin b -> ( try b.run args with Internal m -> internal span m)
  | Keyword k -> (
      match args with
      | [ r ] -> field span k r
      | _ -> internal span "a keyword applied to more than one value")
  | _ -> internal span "calling a value that is not a function"

let eval_def ev name (value : Ast.expr) =
  match value.kind with
  | Fn lambda ->
      (* A generic function is made at each use: it keeps where it was defined. *)
      let source = !source in
      generic value [] (fun locals ->
          Closure { name = Some name; lambda; locals; globals = ev.globals; source })
  | _ -> eval ev value []
