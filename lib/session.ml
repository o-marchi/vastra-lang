(* Runs read → expand → analyze → check → evaluate on a submission. A submission
   is atomic: on any error, none of its definitions are kept.

   Functions find global names when they run (late binding), so a
   redefinition must keep every function that uses it well-typed. When a
   redefinition changes a name's type, the functions that depend on it are
   suspended; at the end of the submission each must still check with its old
   type (or have been redefined), or the submission is rejected. A value was
   computed once and is never computed again, so it keeps its type.

   Code runs against the versions of names it was checked against: a
   redefinition that keeps the type replaces the version, one that changes it
   starts a new version, under a new key, which older code never sees. *)

module Env = Map.Make (String)

type outcome =
  | Defined of { name : string; ty : string }
  | Evaluated of { value : string; ty : string }
  | Declared of string
  | Failed of string * Reader.span (* a task that ended with an error value *)

(* A result and its type: on one line if they fit [width], or the type on a
   line of its own. *)
let typed ?width shown ty =
  match width with
  | Some w
    when String.contains shown '\n' || String.contains ty '\n'
         || Pretty.length shown + 3 + Pretty.length ty > w ->
      shown ^ "\n: " ^ ty
  | _ -> shown ^ " : " ^ ty

let outcome_to_string ?width = function
  | Defined { name; ty } -> typed ?width name ty
  | Evaluated { value; ty } -> typed ?width value ty
  | Declared text -> text
  | Failed (error, _) -> "task failed: " ^ error

(* What the session keeps about a definition, to re-check and export it. [at]
   is the file and line that define it, or None for the prompt. *)
type definition = {
  top : Ast.top;
  deps : string list;
  text : string;
  user : bool;
  at : (string * int) option;
  line : int -> int; (* the line of a byte of the source that defines it *)
}

type suspension = {
  name : string;
  cause : string;
  cause_span : Reader.span;
  old : Types.scheme;
}

type macro = { run : Value.t; params : int; rest : bool }

type state = {
  env : Infer.env;
  values : Value.t ref Env.t; (* cells, by key: see [key] *)
  versions : int Env.t; (* names whose type a redefinition has changed *)
  defs : definition Env.t;
  order : string list; (* first definitions first *)
  suspended : suspension list;
  macros : macro Env.t;
  loaded : string list; (* modules *)
  changers : string list Env.t; (* each file's names its code set!s *)
  handled : (string option * Ast.pattern) list;
      (* the patterns of the page's handlers, in order, and where they come from *)
}

type t = {
  mutable state : state;
  globals : Value.t ref Env.t ref; (* what running code sees *)
  mutable undo : (Value.t ref * Value.t) list; (* cells this submission replaced *)
  max_depth : int;
  mutable trusted : bool; (* the prelude and the standard library may declare natives *)
  mutable run_tasks : bool; (* run top-level tasks (REPL, programs), or just show them *)
  base_dir : string; (* where user modules are found *)
  mutable platform : string; (* "native", or "js" in the browser *)
  mutable trace : (Ast.top * outcome * bool) list option;
      (* when set: every top-level form, its outcome, and whether the program shows
         it (not the prelude's or a required module's), newest first; for Compile *)
  mutable check_only : bool; (* check, but do not evaluate values or expressions *)
  mutable definitions_only : bool; (* check top-level expressions, do not run them *)
  mutable loading : string list; (* the modules being loaded, the innermost first *)
  mutable expressions : (string option * string) list;
      (* the text of the user's top-level expressions in the last accepted submission,
         each with the file it is in (None at the prompt) *)
  mutable file : (string * string) option;
      (* the file the forms being run come from, its name and source; None at the prompt *)
  mutable source : string; (* the source the forms being run come from *)
  mutable changed : string list; (* names the last submission gave a new type *)
  mutable declared : string list; (* the types this submission defined *)
  mutable defined : (string * int) list;
      (* the names this submission defined, with their lines: one each *)
  mutable handlers : Value.handler list; (* what this submission's on forms gave *)
  mutable views : Value.view list; (* and its view forms *)
  mutable ons : (Ast.expr * Reader.span) list; (* and its page handlers, with spans *)
  mutable window : bool; (* whether the last on checked takes window events *)
  mutable restarted : string list; (* values a save started again *)
  mutable fresh : string list;
      (* what a save defined anew: the values it started again, and the functions
         whose lines changed *)
  mutable disputed : int list; (* the names' unknowns a file fixes otherwise *)
  mutable notes : string list; (* what a change of type reset *)
  mutable why : string option; (* the last error's rule, for :why *)
  mutable results : (Value.t * Types.scheme) list;
      (* what the last submission's top-level expressions gave, for *1 *)
  mutable width : int option; (* to lay results out for, in a terminal *)
}

let with_scope st scope = { st with env = { st.env with scope } }

let defined st q =
  Env.mem q st.env.vars || Env.mem q st.macros || Env.mem q st.env.types
  || Env.mem q st.env.ctors || Env.mem q st.env.suspended

(* The global a name refers to: alias/x is x in the aliased module; a plain x
   is the current module's own, a referred name, or a core name. [own] is the
   name being defined, which is the module's even before it exists. *)
let resolve ?own st name =
  match String.index_opt name '/' with
  | _ when String.starts_with ~prefix:"^" name ->
      (* ^map is the core's par/map; a name with none stays, and Infer says so. *)
      let parallel = "par/" ^ String.sub name 1 (String.length name - 1) in
      if defined st parallel then parallel else name
  | Some i when i > 0 && i < String.length name - 1 -> (
      match List.assoc_opt (String.sub name 0 i) st.env.scope.aliases with
      | Some m -> m ^ String.sub name i (String.length name - i)
      | None -> name)
  | _ -> (
      match st.env.scope.module_ with
      | Some m when own = Some name || defined st (m ^ "/" ^ name) -> m ^ "/" ^ name
      | _ -> Option.value (List.assoc_opt name st.env.scope.refers) ~default:name)

let qualify st name =
  match st.env.scope.module_ with Some m -> m ^ "/" ^ name | None -> name

(* A name as you would type it here. *)
let short st = Infer.shown st.env

(* A type as shown here, its unknowns as their uses fixed them. *)
let show st ?width ?col (scheme : Types.scheme) =
  Types.show_scheme ~shown:(short st) ?width ?col
    { scheme with ty = Infer.resolved st.env scheme.ty }

(* How an error names a form that fixed a name's unknown: where it is in
   its file, or as typed at the prompt. *)
let use st (top : Ast.top) text = function
  | Some (file, line) -> Printf.sprintf "at %s:%d" file line
  | None -> (
      match top with
      | Def { name; _ } -> Printf.sprintf "by `%s`" (short st name.name)
      | _ -> "by " ^ text)

(* A name changes only in its own file, since what changes is found by
   reading each file's own code. The prompt changes any name. *)
let own_changes s st (top : Ast.top) =
  let rec go (e : Ast.expr) =
    (match (e.kind, s.file) with
    | Change { target = { kind = Var n; span; _ }; _ }, Some (file, _) -> (
        match Option.bind (Env.find_opt n st.defs) (fun d -> d.at) with
        | Some (owner, line) when owner <> file ->
            Diagnostic.fail
              (Diagnostic.make ~why:"set-names" Type span
                 (Printf.sprintf "`%s` changes only in its own file" (short st n))
              |> Diagnostic.note (Printf.sprintf "it is defined at %s:%d" owner line)
              |> Diagnostic.note "call one of that file's ! functions to change it")
        | _ -> ())
    | _ -> ());
    List.iter go (Ast.children e)
  in
  match top with
  | Def { value = e; _ } | Expr e | On { handler = e; _ } -> go e
  | View v -> List.iter go [ v.place; v.draw ]
  | _ -> ()

(* [top] checked, and the session with what it fixed of the names' types. *)
let checked s st top text (span : Reader.span) =
  let line (file, source) = (file, Diagnostic.line source span.start) in
  let at = Option.map line s.file in
  let scheme, env =
    Infer.check_expr ~disputed:s.disputed ~use:(use st top text at)
      ~line:(Diagnostic.line s.source) st.env top
  in
  own_changes s st top;
  (* A buffer an expression gives back is shown, and kept, as a vector. *)
  let scheme =
    match top with Expr _ -> { scheme with ty = Types.frozen scheme.ty } | _ -> scheme
  in
  (scheme, { st with env })

let resolve_type ?own st = Ast.rename_type (resolve ?own st)

(* Calls are folded here, before type checking, because only resolved
   names tell the core's + from a module's own or one redefined at the prompt;
   locals are left alone by Ast.rename. *)
let operator st (call : Ast.expr) =
  match call.kind with
  | Call { func = { kind = Var op; _ }; _ } when List.mem op Analyze.operators -> (
      match Env.find_opt op st.defs with
      | Some { user = true; _ } -> call
      | _ -> Analyze.operator op call)
  (* A ! added to a call of a function that acts through what it is given. *)
  | Call ({ func = { kind = Var n; _ } as func; _ } as c)
    when Infer.bang n && (not (defined st n)) && defined st (resolve st (Ast.unbang n)) ->
      let plain = resolve st (Ast.unbang n) in
      let func = { func with kind = Var plain; origin = Some "!" } in
      { call with kind = Call { c with func } }
  | _ -> call

let resolve_top st (top : Ast.top) : Ast.top =
  let named (b : Ast.binding) =
    { b with name = qualify st b.name; written = Option.map (resolve_type st) b.written }
  in
  let call = operator st in
  match top with
  | Def { name; doc; value } ->
      let value = Ast.rename (resolve ~own:name.name st) ~call value in
      Def { name = named name; doc; value }
  | Expr e -> Expr (Ast.rename (resolve st) ~call e)
  | Macro m ->
      let bound =
        List.map (fun (b : Ast.binding) -> b.name) (m.params @ Option.to_list m.rest)
      in
      Macro
        { m with name = named m.name; body = Ast.rename (resolve st) ~call ~bound m.body }
  | Type { name; params; ctors; shape } ->
      let ctor (c : Ast.ctor) =
        {
          c with
          ctor_name = qualify st c.ctor_name;
          fields = List.map (resolve_type ~own:name.name st) c.fields;
        }
      in
      let shape = Option.map (resolve_type ~own:name.name st) shape in
      Type { name = named name; params; ctors = List.map ctor ctors; shape }
  | Native { name; ty } -> Native { name = named name; ty = resolve_type st ty }
  | On o -> On { o with handler = Ast.rename (resolve st) ~call o.handler }
  | View v ->
      View
        {
          v with
          place = Ast.rename (resolve st) ~call v.place;
          draw = Ast.rename (resolve st) ~call v.draw;
        }
  | Ns _ -> top

let constructor_value name arity =
  if arity = 0 then Value.Ctor (name, [])
  else Value.Builtin { builtin_name = name; run = (fun args -> Value.Ctor (name, args)) }

(* Where running code finds a global: its name, then a number for each version. *)
let key st name =
  match Env.find_opt name st.versions with
  | Some v -> name ^ " " ^ string_of_int v
  | None -> name

let new_version st name =
  let v = 1 + Option.value (Env.find_opt name st.versions) ~default:0 in
  { st with versions = Env.add name v st.versions }

(* A definition's value as it runs: a function calls itself in its new version;
   a value refers to the version it replaces. *)
let running before after (value : Ast.expr) =
  Ast.rename (key (match value.kind with Fn _ -> after | _ -> before)) value

(* The top-level form as it runs, with keys: what `vastra build` compiles. *)
let ran before after : Ast.top -> Ast.top = function
  | Def ({ name; value; _ } as d) ->
      Def
        {
          d with
          name = { name with name = key after name.name };
          value = running before after value;
        }
  | Expr e -> Expr (Ast.rename (key before) e)
  | On o -> On { o with handler = Ast.rename (key before) o.handler }
  | View v ->
      let keyed = Ast.rename (key before) in
      View { v with place = keyed v.place; draw = keyed v.draw }
  | top -> top

(* Gives the runtime the handlers and views an accepted submission made:
   a file's replace those it made before, and a view replaces the one of its
   place. A submission whose task waits gives them before it ends too. *)
let install s file =
  let mine at = at <> None && at = file in
  if s.handlers <> [] || s.views <> [] || file <> None then (
    let kept (h : Value.handler) = not (mine h.from || List.memq h s.handlers) in
    Value.handlers := List.filter kept !Value.handlers @ s.handlers;
    let replaced (v : Value.view) =
      mine v.at
      || List.exists (fun (w : Value.view) -> Value.same_place v.place w.place) s.views
    in
    Value.views := List.filter (fun v -> not (replaced v)) !Value.views @ s.views;
    !Value.redraw ())

let evaluator s span =
  let ev = { Eval.depth = 0; max_depth = s.max_depth; globals = s.globals } in
  Eval.source := Some (Option.fold ~none:"repl" ~some:fst s.file, s.source);
  (Value.apply := fun f args -> Eval.apply ev f args span);
  (* While a top-level task waits, events reach the handlers so far. *)
  (Eval.waiting := fun () -> install s (Option.map fst s.file));
  ev

(* A definition from the prompt leaves it where a file defines it: the file
   still owns its types. *)
let remember s st name top text deps (span : Reader.span) =
  let order = if Env.mem name st.defs then st.order else st.order @ [ name ] in
  let at =
    match s.file with
    | Some (file, source) -> Some (file, Diagnostic.line source span.start)
    | None -> Option.bind (Env.find_opt name st.defs) (fun d -> d.at)
  in
  {
    st with
    defs =
      Env.add name
        { top; deps; text; user = not s.trusted; at; line = Diagnostic.line s.source }
        st.defs;
    order;
  }

(* At the prompt, a type that a file defines changes only in that file. *)
let owned s st what name span notes =
  match (s.file, Option.bind (Env.find_opt name st.defs) (fun d -> d.at)) with
  | None, Some (file, line) ->
      Diagnostic.fail
        (List.fold_left
           (fun d n -> Diagnostic.note n d)
           (Diagnostic.make ~why:"redefinition" Type span
              (Printf.sprintf "%s `%s` changes only in its file" what (short st name)))
           (Printf.sprintf "it is defined at %s:%d" file line :: notes))
  | _ -> ()

(* A name has one definition in a file, or in one submission at the prompt. *)
let once s st (name : Ast.binding) =
  (match List.assoc_opt name.name s.defined with
  | Some line ->
      Diagnostic.fail
        (Diagnostic.make ~why:"defined-once" Name name.name_span
           (Printf.sprintf "`%s` is already defined, at line %d" (short st name.name)
              line)
        |> Diagnostic.note
             "a name has one definition in a file, or in one submission at the prompt")
  | None -> ());
  s.defined <- (name.name, Diagnostic.line s.source name.name_span.start) :: s.defined

let set_value s st name scheme value =
  let values =
    match Env.find_opt (key st name) st.values with
    | Some cell ->
        (* In place, so stored functions see it too. *)
        s.undo <- (cell, !cell) :: s.undo;
        cell := value;
        st.values
    | None -> Env.add (key st name) (ref value) st.values
  in
  s.globals := values;
  {
    st with
    env =
      {
        st.env with
        vars = Env.add name scheme st.env.vars;
        suspended = Env.remove name st.env.suspended;
      };
    values;
    suspended = List.filter (fun (x : suspension) -> x.name <> name) st.suspended;
  }

(* Suspend every function that depends on [cause], or on the names it [uses]
   (a type's constructors), directly or not. *)
let suspend ?(uses = []) st cause cause_span =
  (* A named map stands for its map, so code that writes it depends on the
     types in it too. Two maps can name each other after a redefinition. *)
  let through = ref [] in
  let rec go st name =
    Env.fold
      (fun d (def : definition) st ->
        let fn =
          match def.top with Def { value = { kind = Fn _; _ }; _ } -> true | _ -> false
        and map = match def.top with Type { shape = Some _; _ } -> true | _ -> false in
        if fn && List.mem name def.deps && Env.mem d st.env.vars then
          let x = { name = d; cause; cause_span; old = Env.find d st.env.vars } in
          (* Only for new code: running code keeps its value. *)
          let st =
            {
              st with
              env =
                {
                  st.env with
                  vars = Env.remove d st.env.vars;
                  suspended = Env.add d cause st.env.suspended;
                };
              suspended = st.suspended @ [ x ];
            }
          in
          go st d
        else if map && List.mem name def.deps && not (List.mem d !through) then (
          through := d :: !through;
          go st d)
        else st)
      st.defs st
  in
  List.fold_left go st (cause :: uses)

(* Does [v], made as a [was] if known, fit [ty]? Values carry their keys and
   constructors, so this looks at them. A function, or any value whose type
   says nothing of its shape, fits only where its type did not change. *)
let rec fits (env : Infer.env) (v : Value.t) was (ty : Types.t) =
  was = Some ty
  ||
  match (ty, v) with
  | Con ("Int", []), Int _
  | Con ("Float", []), Float _
  | Con ("String", []), Str _
  | Con ("Bool", []), Bool _
  | Con ("Unit", []), Unit ->
      true
  | Con (name, []), Fixed (f, _) -> name = Num.name (Fixed f)
  | Unknown (u, _), _ -> (
      match Infer.Ints.find u env.unknowns with
      | Fixed (t, _) -> fits env v was t
      | Open _ -> false)
  | Con ("Vector", [ e; _ ]), Vector vs ->
      let was = match was with Some (Con ("Vector", [ w; _ ])) -> Some w | _ -> None in
      Array.for_all (fun v -> fits env v was e) vs
  | Con ("Dict", [ k; e ]), Dict entries ->
      let wk, we =
        match was with Some (Con ("Dict", [ a; b ])) -> (Some a, Some b) | _ -> (None, None)
      in
      List.for_all (fun (a, b) -> fits env a wk k && fits env b we e) entries
  | Record row, Record fields ->
      let types = Types.fields row in
      let was = match was with Some (Record w) -> Types.fields w | _ -> [] in
      List.length types = List.length fields
      && List.for_all
           (fun (k, t) ->
             match List.assoc_opt k fields with
             | Some v -> fits env v (List.assoc_opt k was) t
             | None -> false)
           types
  | Con (name, args), Ctor (c, vs) -> (
      match Option.bind (Infer.Env.find_opt name env.types) (fun d -> List.assoc_opt c d.ctors) with
      | Some fields when List.length fields = List.length vs ->
          let args = Array.of_list args in
          List.for_all2 (fun f v -> fits env v None (Infer.substitute args f)) fields vs
      | _ -> false)
  | _ -> false

(* What a name keeps when its type changes from [was] to [ty]: records
   key by key, any other value whole if it fits, and the rest from its new
   starting value [start]. Also gives the paths of keys reset, [] for all. *)
let rec keep env (old : Value.t) was ty (start : Value.t) =
  match (was, ty, old, start) with
  | Types.Record w, Types.Record t, Record olds, Record starts when was <> ty ->
      let kept =
        List.map
          (fun (k, s) ->
            match (List.assoc_opt k (Types.fields w), List.assoc_opt k (Types.fields t)) with
            | Some w, Some t ->
                let v, reset = keep env (List.assoc k olds) w t s in
                ((k, v), List.map (fun path -> k :: path) reset)
            | _ -> ((k, s), []))
          starts
      in
      (Value.Record (List.map fst kept), List.concat_map snd kept)
  | _ -> if fits env old (Some was) ty then (old, []) else (start, [ [] ])

(* What the REPL says of a name that kept what fits. *)
let reset_note name = function
  | [] -> []
  | [ [] ] -> [ Printf.sprintf "note: `%s` changed type: it starts again from its new value" name ]
  | paths ->
      let path p = String.concat " " (List.map (( ^ ) ":") p) in
      [
        Printf.sprintf "note: `%s` changed type: %s start%s again from its new value" name
          (String.concat ", " (List.map path paths))
          (if List.length paths = 1 then "s" else "");
      ]

(* Runs macro [m] on the forms of a use, giving the code it expands to. *)
let call_macro s (m : macro) name (items : Reader.node list) span =
  let args = List.tl items in
  let n = List.length args in
  if n < m.params || ((not m.rest) && n > m.params) then
    Diagnostic.fail
      (Diagnostic.make ~why:"arity" Syntax span
         (Printf.sprintf "`%s` expects %s%s, but was given %d" name
            (Diagnostic.plural m.params "form")
            (if m.rest then " or more" else "")
            n));
  let form n = Value.Form n in
  let fixed = List.filteri (fun i _ -> i < m.params) args in
  let extra = List.filteri (fun i _ -> i >= m.params) args in
  let args =
    List.map form fixed
    @ if m.rest then [ Value.Vector (Array.of_list (List.map form extra)) ] else []
  in
  let ev = { Eval.depth = 0; max_depth = s.max_depth; globals = s.globals } in
  (Value.apply := fun f args -> Eval.apply ev f args span);
  Value.site := Some (name, span);
  let result =
    Fun.protect
      ~finally:(fun () -> Value.site := None)
      (fun () -> Eval.apply ev m.run args span)
  in
  match result with
  | Form n | Ctor ("Ok", [ Form n ]) -> n
  | Ctor ("Err", [ Str text ]) ->
      (* The first line is the message, the others are notes. *)
      let message, notes =
        match String.split_on_char '\n' text with
        | m :: notes -> (m, notes)
        | [] -> (text, [])
      in
      Diagnostic.fail
        (List.fold_left
           (fun d n -> Diagnostic.note n d)
           (Diagnostic.make ~why:"form" Syntax span message)
           notes)
  | _ ->
      Eval.internal span ("the macro " ^ name ^ " returned something that is not a Form")

(* The module a file declares, in its first form. *)
let module_of (nodes : Reader.node list) =
  match nodes with
  | { form = List ({ form = Symbol "ns"; _ } :: { form = Symbol m; _ } :: _); _ } :: _ ->
      Some m
  | _ -> None

(* The names a file's code set!s, and where, which a plain function
   cannot read. They are found before the file runs, so a function written
   above the change is refused too. At the prompt only functions and handlers
   count: a set! typed there is a redefinition. *)
let changing st file source (nodes : Reader.node list) =
  let module_ = module_of nodes in
  let qualify n =
    match module_ with Some m when not (String.contains n '/') -> m ^ "/" ^ n | _ -> n
  in
  let target (n : Reader.node) =
    match n.form with
    | List ({ form = Symbol ("set!" | "update!"); _ } :: { form = Symbol x; _ } :: _) ->
        Some x
    | _ -> None
  in
  let found = ref [] in
  let rec scan where (n : Reader.node) =
    let line = Diagnostic.line source n.span.start in
    (match (target n, where) with
    | Some x, Some at ->
        found := (qualify x, Printf.sprintf "%s, line %d" at line) :: !found
    | Some x, None when file <> None ->
        found := (qualify x, Printf.sprintf "at line %d" line) :: !found
    | _ -> ());
    match n.form with
    | List ({ form = Symbol "fn"; _ } :: { form = Symbol f; _ } :: _ as items) ->
        List.iter (scan (Some ("in `" ^ f ^ "`"))) items
    | List ({ form = Symbol "on"; _ } :: _ as items) ->
        List.iter (scan (Some "in a handler")) items
    | List items | Vector items -> List.iter (scan where) items
    | Map entries -> List.iter (fun (k, v) -> scan where k; scan where v) entries
    | _ -> ()
  in
  List.iter (scan None) nodes;
  (* A file's set replaces what it found before; the prompt's adds up. *)
  let before =
    Option.value (Option.bind file (fun f -> Env.find_opt f st.changers)) ~default:[]
  in
  let file = Option.value file ~default:"" in
  let kept = List.fold_left (fun m n -> Env.remove n m) st.env.changing before in
  (* The first change of each name says where. *)
  let changing = List.fold_left (fun m (n, at) -> Env.add n at m) kept !found in
  {
    st with
    env = { st.env with changing };
    changers =
      (let prompt = Option.value (Env.find_opt "" st.changers) ~default:[] in
       Env.add file (List.map fst !found @ if file = "" then prompt else []) st.changers);
  }

(* A top-level form, expanded, analyzed and with its names resolved. *)
let analyze s st node =
  let macro name =
    let q = resolve st name in
    Option.map (fun m -> call_macro s m (short st q)) (Env.find_opt q st.macros)
  in
  (Analyze.is_macro := fun n -> Env.mem (resolve st n) st.macros);
  Lift.top
    (resolve_top st (Analyze.analyze_top ~trusted:s.trusted (Expand.expand ~macro node)))

(* Where a user module's file is: a.b-c is a/b-c.vas, next to the program. *)
let path s module_ =
  let file = String.map (fun c -> if c = '.' then '/' else c) module_ ^ ".vas" in
  if s.base_dir = "." then file else Filename.concat s.base_dir file

(* Reads it, or fails with Sys_error. A page reads it from beside itself. *)
let read = ref (fun path -> In_channel.with_open_bin path In_channel.input_all)

(* An ES module's value, which the JavaScript runtime loaded before the
   program ran, if it did. *)
let imported : (string -> Value.t option) ref = ref (fun _ -> None)

let rec run_form s st source (node : Reader.node) =
  let { Reader.start; stop } = node.span in
  run_node s st (String.sub source start (stop - start)) node

and run_node s st text node =
  let top = analyze s st node in
  let shown = (not s.trusted) && s.loading = [] in
  (match top with
  | Expr _ when not s.trusted ->
      s.expressions <- s.expressions @ [ (Option.map fst s.file, text) ]
  | _ -> ());
  let st', outcome = run_top s st text node top in
  let top = match top with On o -> Ast.On { o with window = s.window } | top -> top in
  Option.iter (fun t -> s.trace <- Some ((ran st st' top, outcome, shown) :: t)) s.trace;
  (st', outcome)

and run_top s st text node top =
  match top with
  | Type { name; params; ctors; shape } ->
      let changed = Infer.changes st.env name params ctors shape in
      if changed then (
        owned s st "the type" name.name name.name_span [];
        (* In one submission a type has one definition, as in a built program. *)
        if List.mem name.name s.declared then
          Diagnostic.fail
            (Diagnostic.make ~why:"defined-once" Type name.name_span
               (Printf.sprintf "the type `%s` is already defined" (short st name.name))
            |> Diagnostic.note
                 "a type has one definition in a file, or in one submission at the prompt"));
      s.declared <- name.name :: s.declared;
      let uses =
        match Env.find_opt (Infer.type_key st.env name.name) st.env.types with
        | Some def -> List.map fst def.ctors
        | None -> []
      in
      let env = Infer.define_type st.env name params ctors shape in
      List.iter
        (fun (c : Ast.ctor) -> Option.iter (Hashtbl.replace Value.words c.ctor_name) c.word)
        ctors;
      let values =
        List.fold_left
          (fun vs (c : Ast.ctor) ->
            Env.add c.ctor_name
              (ref (constructor_value c.ctor_name (List.length c.fields)))
              vs)
          st.values ctors
      in
      s.globals := values;
      let shown =
        String.concat " "
          (short st name.name :: List.map (fun (p : Ast.binding) -> p.name) params)
      in
      let deps = Option.fold shape ~none:[] ~some:Ast.type_names in
      let st = remember s { st with env; values } name.name top text deps node.span in
      if changed then s.changed <- s.changed @ [ short st name.name ];
      ( (if changed then suspend ~uses st name.name name.name_span else st),
        Declared ("type " ^ if params = [] then shown else "(" ^ shown ^ ")") )
  | Native { name; ty } ->
      let scheme = Infer.native_scheme st.env ty in
      let value =
        match List.assoc_opt name.name (Builtins.all @ !Builtins.extra) with
        | Some v -> v
        (* Checking for `vastra build`: the target provides the implementation. *)
        | None when s.check_only -> Value.Unit
        | None ->
            Diagnostic.fail
              (Diagnostic.make ~why:"bug" Name name.name_span
                 ("no native implementation for " ^ name.name))
      in
      ( set_value s st name.name scheme value,
        Defined
          {
            name = short st name.name;
            ty = show st ?width:s.width ~col:2 scheme;
          } )
  | Def { name; value; _ } ->
      once s st name;
      (match value.kind with
      | Run _ when not s.run_tasks ->
          Diagnostic.fail
            (Diagnostic.make ~why:"vastra-file" Command value.span
               (Printf.sprintf
                  "`%s` runs a task to get its value, and `vastra FILE` runs no tasks"
                  (short st name.name))
            |> Diagnostic.note "`vastra run` runs tasks, as does the REPL"
            |> fun d ->
            Option.fold s.file ~none:d ~some:(fun (path, _) ->
                Diagnostic.fix (Run ("vastra run " ^ path)) d))
      | _ -> ());
      let scheme, st = checked s st top text node.span in
      let previous =
        match Env.find_opt name.name st.env.vars with
        | Some p -> Some p
        | None ->
            Option.map
              (fun x -> x.old)
              (List.find_opt (fun (x : suspension) -> x.name = name.name) st.suspended)
      in
      let changed =
        match previous with
        | Some p -> not (Infer.same st.env p scheme)
        | None -> false
      in
      (* The running program's data keeps a shape its file describes. *)
      if changed && Env.mem name.name st.env.changing then
        owned s st "the type of" name.name name.name_span [];
      let after = if changed then new_version st name.name else st in
      let fn = match value.kind with Fn _ -> true | _ -> false in
      let skip = (not fn) && s.check_only in
      (* Saving a file restarts the lines that changed, and the values computed
         from one that restarts, through the functions they call too. A value
         on a line that didn't keeps what it holds, what set! gave included;
         a name the file's code changes is the program's state, so it keeps
         what fits even when what it reads restarts. *)
      let deps = List.filter (( <> ) name.name) (Ast.references value) in
      let seen = Hashtbl.create 16 in
      let rec stale n =
        List.mem n s.fresh
        || (not (Hashtbl.mem seen n))
           && (Hashtbl.add seen n ();
               match Env.find_opt n st.defs with
               | Some { top = Def { value = { kind = Fn _; _ }; _ }; deps; _ } ->
                   List.exists stale deps
               | _ -> false)
      in
      let same_text =
        match (s.file, Env.find_opt name.name st.defs) with
        | Some (file, _), Some { text = t; at = Some (f, _); _ } -> t = text && f = file
        | _ -> false
      in
      let same_line =
        same_text && (not fn)
        && (Env.mem name.name st.env.changing || not (List.exists stale deps))
      in
      let kept =
        if same_line && Option.is_some previous && not changed then
          Env.find_opt (key st name.name) st.values
        else None
      in
      (* A function on a line that didn't change is the same, and so is a value
         made again only for its new type. *)
      if not (same_line || (fn && same_text)) then s.fresh <- name.name :: s.fresh;
      (match (kept, value.kind, s.file) with
      | None, (Fn _), _ | _, _, None -> ()
      | None, _, Some _ when Option.is_some previous ->
          s.restarted <- s.restarted @ [ short st name.name ]
      | _ -> ());
      let v =
        match kept with
        | Some cell -> !cell
        | None when skip -> Value.Unit
        | None -> (
            let v =
              Eval.eval_def (evaluator s node.span) name.name (running st after value)
            in
            (* A name the file changes, on a line that didn't change, whose type
               did: it keeps what fits. *)
            match (previous, Env.find_opt (key st name.name) st.values) with
            | Some p, Some { contents = old }
              when same_line && changed && Env.mem name.name st.env.changing ->
                let v, reset = keep st.env old p.ty scheme.ty v in
                s.notes <- s.notes @ reset_note (short st name.name) reset;
                v
            | _ -> v)
      in
      let st =
        remember s (set_value s after name.name scheme v) name.name top text deps node.span
      in
      if changed then s.changed <- s.changed @ [ short st name.name ];
      let st = if changed then suspend st name.name node.span else st in
      ( st,
        Defined
          {
            name = short st name.name;
            ty = show st ?width:s.width ~col:2 scheme;
          } )
  | Macro { name; params; rest; body; _ } ->
      once s st name;
      Infer.check_macro st.env params rest body;
      let all = params @ Option.to_list rest in
      let bound = List.map (fun (b : Ast.binding) -> b.name) all in
      let lambda = { Ast.params = all; body = Ast.rename (key st) ~bound body } in
      let run =
        Value.Closure
          { name = None; lambda; locals = []; globals = s.globals; source = !Eval.source }
      in
      let m = { run; params = List.length params; rest = rest <> None } in
      let st = { st with macros = Env.add name.name m st.macros } in
      ( remember s st name.name top text (Ast.references body) node.span,
        Declared ("macro " ^ short st name.name) )
  | Ns { name; requires; targets; imports } ->
      if targets <> [] && not (List.mem s.platform targets) then
        Diagnostic.fail
          (Diagnostic.make ~why:"modules" Name node.span
             (Printf.sprintf "the module %s runs only on %s, not on %s" name
                (String.concat ", " targets) s.platform));
      let st = with_scope st { module_ = Some name; aliases = []; refers = [] } in
      let st = List.fold_left (require s) st requires in
      (List.fold_left (import s) st imports, Declared ("module " ^ name))
  (* A handler and a view: made now, and given to the runtime when the
     submission is accepted. *)
  | On o ->
      let scheme, st = checked s st top text node.span in
      s.window <-
        (match scheme.ty with
        | Fun ([ Con (e, []) ], _, _) -> e = Infer.type_key st.env "vastra.window/Event"
        | _ -> false);
      if not s.check_only then (
        let handler = Ast.rename (key st) o.handler in
        let handle = Eval.eval (evaluator s node.span) handler [] in
        let from = Option.map fst s.file in
        s.handlers <- s.handlers @ [ { Value.from; window = s.window; handle } ]);
      if not s.window then s.ons <- s.ons @ [ (o.handler, node.span) ];
      (st, Declared ("on " ^ o.shown))
  | View v ->
      let _, st = checked s st top text node.span in
      if not s.check_only then (
        let eval e = Eval.eval (evaluator s node.span) (Ast.rename (key st) e) [] in
        let place = eval v.place and draw = eval v.draw in
        s.views <- s.views @ [ { Value.at = Option.map fst s.file; place; draw } ]);
      (st, Declared ("view " ^ v.shown))
  | Expr _ when s.check_only || s.definitions_only ->
      let scheme, st = checked s st top text node.span in
      ( st,
        Evaluated
          {
            value = "";
            ty = show st ?width:s.width ~col:2 scheme;
          } )
  | Expr e ->
      let scheme, st = checked s st top text node.span in
      let v = Eval.eval (evaluator s node.span) (Ast.rename (key st) e) [] in
      match (Value.frozen v, scheme.ty) with
      | Task run, Con ("Task", [ _; result ]) when s.run_tasks -> (
          match Eval.run_top run with
          | Some (Ok v) ->
              let v = Value.frozen v in
              if s.loading = [] then
                s.results <- s.results @ [ (v, { scheme with ty = result }) ];
              ( st,
                Evaluated
                  {
                    value = Value.to_string ~name:(short st) ?width:s.width v;
                    ty =
                      show st ?width:s.width ~col:2
                        { scheme with ty = result };
                  } )
          | Some (Error err) ->
              (st, Failed (Value.to_string ~name:(short st) err, node.span))
          | None -> (st, Declared "task started"))
      | v, _ ->
          if s.loading = [] then s.results <- s.results @ [ (v, scheme) ];
          ( st,
            Evaluated
              {
                value = Value.to_string ~name:(short st) ?width:s.width v;
                ty = show st ?width:s.width ~col:2 scheme;
              } )

(* An ES module, named in this module as a js/Value. *)
and import s st (i : Ast.import) =
  if s.platform <> "js" then
    Diagnostic.fail
      (Diagnostic.make ~why:"modules" Name i.import_at
         "an ES module is imported only where JavaScript runs"
      |> Diagnostic.note "a module that imports one says (:target :js)");
  let js = { Ast.module_ = "vastra.js"; alias = None; refer = []; at = i.import_at } in
  let st = require s st js in
  let value =
    match !imported i.spec with
    | Some v -> v
    (* Checking for `vastra build`: the program loads it when it starts. *)
    | None when s.check_only -> Value.Unit
    | None ->
        Diagnostic.fail
          (Diagnostic.make ~why:"modules" Name i.import_at (i.spec ^ " is not loaded")
          |> Diagnostic.note "a page loads its ES modules when it starts: reload it")
  in
  let span = i.import_at in
  let ty = { Reader.form = Symbol "vastra.js/Value"; span; origin = None } in
  set_value s st (qualify st i.local) (Infer.native_scheme st.env ty) value

(* Brings a module into scope, loading it first if needed. *)
and require s st (r : Ast.require) =
  (* The plain minimum: files that require each other are not decided yet. *)
  if List.mem r.module_ s.loading then
    Diagnostic.fail
      (Diagnostic.make ~why:"modules" Name r.at
         (Printf.sprintf "%s and %s require each other" r.module_
            (Option.value st.env.scope.module_ ~default:"this file"))
      |> Diagnostic.note "files that require each other, even through others, can't run");
  let st = if List.mem r.module_ st.loaded then st else load s st r in
  let refer n =
    let q = r.module_ ^ "/" ^ n in
    if not (defined st q) then
      Diagnostic.fail
        (Diagnostic.make ~why:"modules" Name r.at
           (Printf.sprintf "the module %s has no `%s`" r.module_ n));
    (n, q)
  in
  let aliases =
    match r.alias with
    | Some a -> (a, r.module_) :: st.env.scope.aliases
    | None -> st.env.scope.aliases
  in
  with_scope st
    { st.env.scope with aliases; refers = List.map refer r.refer @ st.env.scope.refers }

(* A module comes from the standard library, or from a file under the
   program's directory: the module a.b-c is a/b-c.vas. *)
and load s st (r : Ast.require) =
  let path = path s r.module_ in
  let source, origin =
    match Stdlib_sources.find r.module_ with
    | Some source -> (source, r.module_)
    | None -> (
        match !read path with
        | source -> (source, path)
        | exception Sys_error _ ->
            Diagnostic.fail
              (Diagnostic.make ~why:"modules" Name r.at
                 ("cannot find the module " ^ r.module_)
              |> Diagnostic.note ("looked in the standard library and for " ^ path)))
  in
  let outer = st.env.scope in
  let st =
    {
      (with_scope st { module_ = Some r.module_; aliases = []; refers = [] }) with
      loaded = r.module_ :: st.loaded;
    }
  in
  let in_file (d : Diagnostic.t) =
    if d.file = None then { d with file = Some (origin, source) } else d
  in
  (* A module for another platform is refused at the require, before it runs. *)
  (match Reader.read_all source with
  | Ok (first :: _) -> (
      match Analyze.analyze_top ~trusted:true first with
      | Ns { targets; _ } when targets <> [] && not (List.mem s.platform targets) ->
          Diagnostic.fail
            (Diagnostic.make ~why:"modules" Name r.at
               (Printf.sprintf "the module %s runs only on %s, not on %s" r.module_
                  (String.concat ", " targets) s.platform))
      | _ -> ()
      | exception Diagnostic.Error _ -> ())
  | _ -> ());
  let was_trusted = s.trusted and was_file = s.file and was_source = s.source in
  s.trusted <- Option.is_some (Stdlib_sources.find r.module_);
  s.loading <- r.module_ :: s.loading;
  s.file <- Some (origin, source);
  s.source <- source;
  let st =
    try
      match Reader.read_all source with
      | Error e -> raise (Diagnostic.Error (Diagnostic.of_read_error e))
      | Ok nodes ->
          let st = changing st (Some origin) source nodes in
          List.fold_left (fun st node -> fst (run_form s st source node)) st nodes
    with Diagnostic.Error d ->
      s.trusted <- was_trusted;
      s.loading <- List.tl s.loading;
      s.file <- was_file;
      s.source <- was_source;
      raise (Diagnostic.Error (in_file d))
  in
  s.trusted <- was_trusted;
  s.loading <- List.tl s.loading;
  s.file <- was_file;
  s.source <- was_source;
  if st.env.scope.module_ <> Some r.module_ then
    Diagnostic.fail
      (Diagnostic.make ~why:"modules" Name r.at
         (Printf.sprintf "%s declares itself as %s" origin
            (Option.value st.env.scope.module_ ~default:"no module")));
  with_scope st outer

(* A type's constructors, if [name] is a type. *)
let constructors st name =
  match (Env.find name st.defs).top with
  | Type _ -> (
      match Env.find_opt (Infer.type_key st.env name) st.env.types with
      | Some t -> List.map fst t.ctors
      | None -> [])
  | _ -> []

(* Takes a name out of the session: new code no longer reaches it. Its cell
   stays for code already running, under a version nothing reuses. *)
let drop st name =
  let ctors = constructors st name and env = st.env in
  let types =
    match (Env.find name st.defs).top with
    | Type _ -> Env.remove (Infer.type_key env name) env.types
    | _ -> env.types
  in
  let st = new_version st name in
  {
    st with
    defs = Env.remove name st.defs;
    order = List.filter (( <> ) name) st.order;
    macros = Env.remove name st.macros;
    suspended = List.filter (fun (x : suspension) -> x.name <> name) st.suspended;
    env =
      {
        env with
        vars = Env.remove name env.vars;
        suspended = Env.remove name env.suspended;
        types;
        ctors = List.fold_left (fun m c -> Env.remove c m) env.ctors ctors;
      };
  }

(* Restore the suspended definitions that still check. One that checks with a
   new type takes it, in a new version, and its own dependents, already
   suspended, are checked against it. *)
let rec restore s st =
  let check (x : suspension) =
    let def = Env.find x.name st.defs in
    try
      ( x,
        Ok
          (Infer.check_expr ~use:(use st def.top def.text def.at) ~line:def.line st.env
             def.top) )
    with Diagnostic.Error d -> (x, Error d)
  in
  let attempts = List.map check st.suspended in
  match List.find_map (function x, Ok r -> Some (x, r) | _ -> None) attempts with
  | Some (x, (scheme, env)) ->
      let st = { st with env } in
      let changed = not (Infer.same env scheme x.old) in
      let st = if changed then new_version st x.name else st in
      if changed then s.changed <- s.changed @ [ short st x.name ];
      (* A function is made again, so it calls what the submission redefined;
         a value keeps what it was computed with. *)
      let value =
        match (Env.find x.name st.defs).top with
        | Def ({ name; value = { kind = Fn _; _ } as e; _ } as d) ->
            let e = running st st e in
            let top =
              Ast.Def { d with name = { name with name = key st x.name }; value = e }
            in
            Option.iter
              (fun t -> s.trace <- Some ((top, Declared "", false) :: t))
              s.trace;
            Eval.eval_def (evaluator s x.cause_span) x.name e
        | _ -> !(Env.find (key st x.name) st.values)
      in
      restore s (set_value s st x.name scheme value)
  | None -> (
      (* After a file changed, a function typed at the prompt that no longer
         checks is removed: an experiment never blocks the files. Its
         name starts a new version, so nothing reuses what running code has. *)
      let typed (x, _) = s.file <> None && (Env.find x.name st.defs).at = None in
      match List.partition typed attempts with
      | (_ :: _ as typed), [] ->
          let remove st ((x : suspension), result) =
            (match result with
            | Error (d : Diagnostic.t) ->
                s.notes <-
                  s.notes
                  @ [
                      Printf.sprintf
                        "note: removed `%s`, typed at the prompt, which no longer checks: %s"
                        (short st x.name) d.message;
                    ]
            | Ok _ -> ());
            drop st x.name
          in
          List.fold_left remove st typed
      | _, (x, Error d) :: _ ->
          Diagnostic.fail
            (Diagnostic.make ~why:"redefinition" Type x.cause_span
               (Printf.sprintf "redefining `%s` breaks `%s`" (short st x.cause)
                  (short st x.name))
            |> Diagnostic.note (Printf.sprintf "in `%s`: %s" (short st x.name) d.message)
            |> Diagnostic.note
                 (Printf.sprintf "redefine `%s` in the same submission to change both"
                    (short st x.name)))
      | _ -> st)

(* After a file runs, the names it defined and no longer defines are dropped,
   and so is the code typed at the prompt that uses them, which the notes name:
   the file is the source of truth. *)
let forget s st file =
  let now = List.map fst s.defined @ s.declared in
  let stale =
    Env.fold
      (fun name (d : definition) names ->
        match d.at with
        | Some (f, _) when f = file && d.user && not (List.mem name now) -> name :: names
        | _ -> names)
      st.defs []
  in
  let rec go st = function
    | [] -> st
    | name :: rest when not (Env.mem name st.defs) -> go st rest
    | name :: rest ->
        let uses = name :: constructors st name in
        let uses_one (d : definition) = List.exists (fun u -> List.mem u d.deps) uses in
        let users =
          Env.fold
            (fun user (d : definition) users ->
              if d.at = None && uses_one d && not (List.mem user rest) then user :: users
              else users)
            st.defs []
        in
        List.iter
          (fun user ->
            s.notes <-
              s.notes
              @ [
                  Printf.sprintf
                    "note: removed `%s`, typed at the prompt, which used `%s`"
                    (short st user) (short st name);
                ])
          users;
        go (drop st name) (users @ rest)
  in
  go st stale

(* A file's handlers are one match: the first that matches takes the
   message, so an on that can never run is an error, and so is a message of
   the file's that none takes. One typed at the prompt comes after the file's.
   And a handler that leads, before it waits, to sending a message that comes
   back to it would never stop. *)
let one_match s st file =
  (* A file's handlers replace those it had; the prompt's add up. *)
  let replaced from = file <> None && from = file in
  let pattern (handler, _) = Option.get (Ast.handler_pattern handler) in
  let others =
    List.filter_map (fun (from, p) -> if replaced from then None else Some p) st.handled
  in
  let ours = List.map pattern s.ons in
  let signature = Infer.signature st.env in
  (match (file, List.rev s.ons) with
  | Some _, (_, last) :: _ -> Exhaustive.check ~clauses:`Handlers signature ours last
  | None, _ :: _ ->
      (* At the prompt, after the file's: only one that can never run is wrong. *)
      let rec each before = function
        | p :: rest ->
            let all = before @ [ p ] in
            (try Exhaustive.check ~clauses:`Handlers signature all p.Ast.pat_span
             with Diagnostic.Error d when d.message <> "this on can never run" -> ());
            each (before @ [ p ]) rest
        | [] -> ()
      in
      each others ours
  | _ -> ());
  (* Who takes a message, by its constructor: the first on whose pattern can. *)
  let ons = List.map (fun (h, span) -> (pattern (h, span), h, span)) s.ons in
  let taker c =
    List.find_index
      (fun ((p : Ast.pattern), _, _) ->
        match p.pat with PCtor (k, _) -> k = c | PWild | PVar _ -> true | _ -> false)
      ons
  in
  let rec sends seen e =
    List.concat_map
      (function
        | `Sends c -> [ c ]
        | `Calls f when not (List.mem f seen) -> (
            match Env.find_opt f st.defs with
            | Some { top = Def { value = { kind = Fn l; _ }; _ }; _ } ->
                sends (f :: seen) l.body
            | _ -> [])
        | `Calls _ -> [])
      (Ast.before_waiting e)
  in
  let next i =
    let _, h, _ = List.nth ons i in
    List.filter_map
      (fun c -> Option.map (fun j -> (c, j)) (taker c))
      (Option.fold (Ast.handler_body h) ~none:[] ~some:(sends []))
  in
  let name i =
    match (let p, _, _ = List.nth ons i in p.pat) with
    | PCtor (c, _) -> "`" ^ short st c ^ "`'s handler"
    | _ -> "the handler that takes any message"
  in
  (* A path from [i] back to [start], as the messages sent along it. *)
  let rec back start seen i =
    List.find_map
      (fun (c, j) ->
        if j = start then Some [ c ]
        else if List.mem j seen then None
        else Option.map (fun path -> c :: path) (back start (j :: seen) j))
      (next i)
  in
  List.iteri
    (fun i (_, _, span) ->
      match back i [ i ] i with
      | Some (c :: rest) ->
          let whose c = Printf.sprintf ", whose handler sends `%s`" (short st c) in
          let text =
            String.concat ""
              (Printf.sprintf "%s sends `%s`" (name i) (short st c)
              :: List.map whose rest)
          in
          Diagnostic.fail
            (Diagnostic.make ~why:"messages" Type span (text ^ ", and would never stop")
            |> Diagnostic.note
                 "a handler that waits first, with an @, is a retry, and is fine")
      | _ -> ())
    ons;
  {
    st with
    handled =
      List.filter (fun (from, _) -> not (replaced from)) st.handled
      @ List.map (fun p -> (file, p)) ours;
  }

(* An error raised while code ran (a timer's, say), shown in the source of the
   code that raised it. *)
let render_running (d : Diagnostic.t) =
  match !Eval.source with
  | Some (origin, text) -> Diagnostic.render d text origin
  | None -> Diagnostic.render { d with span = Diagnostic.nowhere } "" ""

(* A runtime error in a function read from another file or submission is
   shown in that source. *)
let running_elsewhere s (d : Diagnostic.t) =
  match !Eval.source with
  | Some (_, text) as there when d.phase = Runtime && d.file = None && text != s.source ->
      { d with file = there }
  | _ -> d

(* With [keep] false, everything is put back even when the submission
   succeeds: for checking. [fresh] is what the save defined anew in the files
   it took before this one. *)
let rec eval_source ?(keep = true) ?(fresh = []) ?file s source =
  Value.assigned := Some [];
  Eval.source := None;
  s.file <- Option.map (fun f -> (f, source)) file;
  s.source <- source;
  let state = s.state and expressions = s.expressions in
  s.expressions <- [];
  s.changed <- [];
  s.declared <- [];
  s.defined <- [];
  s.handlers <- [];
  s.views <- [];
  s.ons <- [];
  s.restarted <- [];
  s.fresh <- fresh;
  s.notes <- [];
  s.results <- [];
  let attempt () =
    match Reader.read_all source with
    | Error e -> Error (Diagnostic.of_read_error e)
    | Ok nodes ->
        let st = changing s.state file source nodes in
        (* A file sets its messages again: a save may change their type. *)
        let st =
          if file = None then st else { st with env = { st.env with messages = None } }
        in
        let st = ref st in
        let step node =
          let next, outcome = run_form s !st source node in
          st := next;
          outcome
        in
        let outcomes = Util.map_in_order step nodes in
        let st = restore s !st in
        let st = Option.fold ~none:st ~some:(forget s st) file in
        s.state <- one_match s st file;
        Ok outcomes
  in
  let result =
    try attempt () with
    | Diagnostic.Error d -> Error (running_elsewhere s d)
    | Stack_overflow ->
        Error
          (Diagnostic.make ~why:"depth" Runtime Diagnostic.nowhere
             "evaluation is nested too deeply (native stack exhausted)")
    | e -> Error (Diagnostic.bug Diagnostic.nowhere (Printexc.to_string e))
  in
  (* An atomic submission: a failed one puts back the cells it replaced and the
     names it changed. *)
  let assigned = Option.value !Value.assigned ~default:[] in
  Value.assigned := None;
  if Result.is_error result || not keep then (
    List.iter (fun (cell, v) -> cell := v) assigned;
    List.iter (fun (cell, v) -> cell := v) s.undo;
    s.expressions <- expressions);
  if not keep then s.state <- state;
  s.undo <- [];
  s.globals := s.state.values;
  match result with
  | Ok outcomes ->
      if keep then (
        install s file;
        Value.handle_sent ();
        (* A window this opened runs its frames now. *)
        let loop = !Value.loop in
        Value.loop := ignore;
        loop ());
      Ok outcomes
  (* A file that fixes a name's type otherwise than before takes it over:
     it runs again, its definition leaving that part behind, which
     changes its type, so it keeps what fits. *)
  | Error { against = Some (name, u); _ }
    when file <> None && List.mem_assoc name s.defined && not (List.mem u s.disputed) ->
      s.disputed <- u :: s.disputed;
      let result = eval_source ~keep ~fresh ?file s source in
      s.disputed <- List.filter (( <> ) u) s.disputed;
      result
  | Error d -> Error d

(* What [source] would give, checked without running it, with nothing kept.
   Expressions give their types, with no value. *)
let check s source =
  let results = s.results and changed = s.changed in
  s.check_only <- true;
  let result = eval_source ~keep:false s source in
  s.check_only <- false;
  s.results <- results;
  s.changed <- changed;
  result

(* The files of the user's modules the program loaded. *)
let files s =
  List.filter_map
    (fun m -> if Stdlib_sources.find m = None then Some (path s m) else None)
    s.state.loaded

let create ?(max_depth = 250) ?(base_dir = ".") ?(trace = false) () =
  let empty =
    {
      env = Infer.empty_env;
      values = Env.empty;
      versions = Env.empty;
      defs = Env.empty;
      order = [];
      suspended = [];
      macros = Env.empty;
      loaded = [];
      changers = Env.empty;
      handled = [];
    }
  in
  let s =
    {
      state = empty;
      globals = ref Env.empty;
      undo = [];
      max_depth;
      trusted = true;
      run_tasks = false;
      base_dir;
      platform = "native";
      trace = None;
      check_only = false;
      definitions_only = false;
      expressions = [];
      file = None;
      source = "";
      changed = [];
      declared = [];
      defined = [];
      handlers = [];
      views = [];
      ons = [];
      window = false;
      restarted = [];
      fresh = [];
      disputed = [];
      notes = [];
      why = None;
      results = [];
      loading = [];
      width = None;
    }
  in
  if trace then s.trace <- Some [];
  match eval_source ~file:"prelude" s Prelude_source.source with
  | Ok _ ->
      s.trusted <- false;
      s
  | Error d ->
      failwith
        ("the prelude does not load:\n"
        ^ Diagnostic.render d Prelude_source.source "prelude")

(* -- For the REPL ---------------------------------------------------------- *)

(* The type of an expression, without evaluating it. *)
let type_of_source s source =
  let whole = { Reader.start = 0; stop = String.length source } in
  try
    match Reader.read_all source with
    | Error e -> Error (Diagnostic.of_read_error e)
    | Ok [ node ] -> (
        match analyze s s.state node with
        | Expr _ as top ->
            Ok
              (show s.state ?width:s.width ~col:2
                 (fst
                    (Infer.check_expr ~general:true ~use:"" ~line:(Diagnostic.line source)
                       s.state.env top)))
        | _ -> Error (Diagnostic.make ~why:"form" Syntax node.span
                        ":type takes an expression"))
    | Ok _ -> Error (Diagnostic.make ~why:"form" Syntax whole
                       ":type takes one expression")
  with Diagnostic.Error d -> Error d

(* A definition's type and documentation, by its name as typed here. *)
let doc s name =
  let q = resolve s.state name in
  Option.map
    (fun scheme ->
      let doc =
        match Env.find_opt q s.state.defs with
        | Some { top = Def { doc = Some d; _ }; _ } -> "\n  " ^ d
        | _ -> ""
      in
      name ^ " : " ^ show s.state scheme ^ doc)
    (Env.find_opt q s.state.env.vars)

(* Names as they would be typed here: the current module's own without its
   prefix, other modules' through their alias. *)
let names s =
  let st = s.state in
  let keys m = List.map fst (Env.bindings m) in
  let typed n =
    let aliased =
      List.filter_map
        (fun (alias, m) ->
          if String.starts_with ~prefix:(m ^ "/") n then
            Some
              (alias ^ String.sub n (String.length m) (String.length n - String.length m))
          else None)
        st.env.scope.aliases
    in
    (* Qualified names of other modules stay typable, besides their alias. *)
    let own = Option.map (fun m -> m ^ "/") st.env.scope.module_ in
    (if Option.fold own ~none:false ~some:(fun p -> String.starts_with ~prefix:p n) then
       short st n
     else n)
    :: aliased
  in
  List.concat_map typed (keys st.env.vars @ keys st.env.ctors @ keys st.macros)
  @ List.map fst st.env.scope.refers

(* A definition as :save writes it: as typed, except a copy of a moment of the
   session, one that read a name the code changes or took *1, *2 or *3.
   From a file its text would compute something else, so its value is written,
   when it can be written as code. *)
let source st name =
  let def = Env.find name st.defs in
  let moment d = Env.mem d st.env.changing || List.mem d [ "*1"; "*2"; "*3" ] in
  match def.top with
  | Def { value = { kind = Fn _; _ }; _ } -> def.text
  | Def { doc; _ } ->
      let v = !(Env.find (key st name) st.values) in
      if List.exists moment def.deps && Value.is_code v then
        let doc = match doc with Some d -> "\"" ^ Value.escape d ^ "\" " | None -> "" in
        let name = short st name in
        Printf.sprintf "(let %s %s%s)" name doc (Value.to_string ~name:(short st) v)
      else def.text
  | _ -> def.text

(* The names the file's code changes, by their own names, and their cells: what
   a recording starts from. *)
let cells s =
  let st = s.state in
  Env.fold
    (fun n _ acc ->
      match Env.find_opt (key st n) st.values with
      | Some cell -> (List.hd (List.rev (String.split_on_char '/' n)), cell) :: acc
      | None -> acc)
    st.env.changing []

(* The user's definitions as source, types first, each after what it uses. *)
let export s =
  let user = List.filter (fun n -> (Env.find n s.state.defs).user) s.state.order in
  let is_type n =
    match (Env.find n s.state.defs).top with Type _ -> true | _ -> false
  in
  let types, values = List.partition is_type user in
  let rec sorted done_ = function
    | [] -> List.rev done_
    | pending ->
        let ready, rest =
          List.partition
            (fun n ->
              List.for_all
                (fun d -> List.mem d done_ || not (List.mem d pending))
                (Env.find n s.state.defs).deps)
            pending
        in
        if ready = [] then List.rev_append done_ pending
        else sorted (List.rev_append ready done_) rest
  in
  String.concat "\n\n" (List.map (source s.state) (types @ sorted [] values)) ^ "\n"

(* *1, *2, *3, defined as a definition would be: code that uses one keeps
   the version it was checked against if a later value has another type. *)
let define_result s name (value, scheme) =
  let st = s.state in
  let st =
    match Env.find_opt name st.env.vars with
    | Some p when not (Infer.same st.env p scheme) -> new_version st name
    | _ -> st
  in
  s.state <- set_value s st name scheme value;
  s.undo <- []

let push_result s result =
  let st = s.state in
  let previous n =
    Option.map
      (fun scheme -> (!(Env.find (key st n) st.values), scheme))
      (Env.find_opt n st.env.vars)
  in
  let one = previous "*1" and two = previous "*2" in
  Option.iter (define_result s "*3") two;
  Option.iter (define_result s "*2") one;
  define_result s "*1" result

(* :dir: the session's own definitions, or every name starting with a
   prefix, each with its type; a name the code changes also shows its live
   value. *)
let dir s prefix =
  let st = s.state in
  let line (typed, q) =
    match Env.find_opt q st.env.vars with
    | Some scheme ->
        let value =
          match Env.find_opt (key st q) st.values with
          | Some { contents = v } when Env.mem q st.env.changing ->
              "  = " ^ Value.to_string ~name:(short st) v
          | _ -> ""
        in
        Some (typed ^ " : " ^ show st scheme ^ value)
    | None when Env.mem q st.macros -> Some (typed ^ " : a macro")
    | None when Env.mem q st.env.types -> Some (typed ^ " : a type")
    | None ->
        Option.map
          (fun t -> typed ^ " : a constructor of " ^ short st t)
          (Env.find_opt q st.env.ctors)
  in
  (* Each found by its own name, and written short unless that reaches another;
     with a prefix, as typed. *)
  let written q = if resolve st (short st q) = q then short st q else q in
  let names =
    if prefix = "" then
      List.map
        (fun q -> (written q, q))
        (List.filter (fun n -> (Env.find n st.defs).user) st.order)
    else
      List.map
        (fun t -> (t, resolve st t))
        (List.sort_uniq compare (List.filter (String.starts_with ~prefix) (names s)))
  in
  String.concat "\n" (List.filter_map line names)

(* What a REPL request gives. Its terminal shows each part in its own
   way; piped input prints [text]. [Output] is what tasks printed, in a page. *)
type problem = {
  label : string; (* "type error", or "" when there is no place to show *)
  message : string;
  start : int; (* a span of the submitted source; empty if none *)
  stop : int;
  notes : string list;
  text : string; (* with the source line and carets *)
}

type part = Outcome of outcome | Problem of problem | Note of string | Output of string

let refused message =
  Problem { label = ""; message; start = 0; stop = 0; notes = []; text = message }

let problem source (d : Diagnostic.t) =
  let here = d.file = None && d.span.start >= 0 in
  Problem
    {
      label = Diagnostic.label d.phase;
      message = d.message;
      start = (if here then d.span.start else 0);
      stop = (if here then d.span.stop else 0);
      notes = d.notes @ Diagnostic.tried d source;
      text = Diagnostic.render ~on_screen:true d source "repl";
    }

let text = function
  | Outcome o -> outcome_to_string o
  | Problem p -> p.text
  | Note t | Output t -> t

(* A REPL request: the same whether the session is here or in a web page.
   A request may end with the width to lay what it shows out for: "eval 100". *)
let respond s request arg =
  (* A Ctrl+C is for what was running when it came. *)
  Atomic.set Eval.stop false;
  let request, width =
    match String.split_on_char ' ' request with
    | [ r; w ] -> (r, int_of_string_opt w)
    | _ -> (request, None)
  in
  s.width <- (if request = "eval" || request = "type" then width else None);
  let problem source (d : Diagnostic.t) =
    s.why <- Some d.why;
    problem source d
  in
  match request with
  | "eval" -> (
      match eval_source s arg with
      | Ok outcomes ->
          List.iter (push_result s) s.results;
          List.map (fun o -> Outcome o) outcomes @ List.map (fun n -> Note n) s.notes
      | Error d -> [ problem arg d ])
  | "peek" -> (
      (* A value for the REPL to open: evaluated, but not kept as *1. *)
      match eval_source s arg with
      | Ok outcomes -> List.map (fun o -> Outcome o) outcomes
      | Error d -> [ problem arg d ])
  | "check" -> (
      match check s arg with
      | Ok outcomes -> List.map (fun o -> Outcome o) outcomes
      | Error d -> [ problem arg d ])
  | "dir" ->
      List.map
        (fun l -> Note l)
        (List.filter (( <> ) "") (String.split_on_char '\n' (dir s arg)))
  | "type" -> (
      match type_of_source s arg with
      | Ok ty -> [ Note ty ]
      | Error d -> [ problem arg d ])
  | "doc" -> (
      match doc s arg with
      | Some text -> [ Note text ]
      | None -> [ refused (Printf.sprintf "no definition named `%s`" arg) ])
  | "save" -> [ Note (export s) ]
  | "why" -> (
      match Option.map Why.explain s.why with
      | Some (Some text) -> [ Note text ]
      | Some None -> [ refused "the last error has no long form yet" ]
      | None -> [ refused "no error yet" ])
  | _ -> [ refused ("unknown request " ^ request) ]

(* Parts as text and back, a line each, for a page's answers to vastra serve. *)
let encode parts =
  String.concat "\n"
    (List.map
       (function
         | Outcome (Defined { name; ty }) -> Printf.sprintf "defined %S %S" name ty
         | Outcome (Evaluated { value; ty }) -> Printf.sprintf "evaluated %S %S" value ty
         | Outcome (Declared t) -> Printf.sprintf "declared %S" t
         | Outcome (Failed (e, _)) -> Printf.sprintf "failed %S" e
         | Problem p ->
             Printf.sprintf "problem %S %S %d %d %S %S" p.label p.message p.start p.stop
               (String.concat "\n" p.notes) p.text
         | Note t -> Printf.sprintf "note %S" t
         | Output t -> Printf.sprintf "output %S" t)
       parts)

let decode text =
  let part line =
    Scanf.sscanf line "%s %[^\n]" (fun kind rest ->
        let read format = Scanf.sscanf rest format in
        match kind with
        | "defined" -> read "%S %S" (fun name ty -> Outcome (Defined { name; ty }))
        | "evaluated" -> read "%S %S" (fun value ty -> Outcome (Evaluated { value; ty }))
        | "declared" -> read "%S" (fun t -> Outcome (Declared t))
        | "failed" -> read "%S" (fun e -> Outcome (Failed (e, Diagnostic.nowhere)))
        | "problem" ->
            read "%S %S %d %d %S %S" (fun label message start stop notes text ->
                let notes = if notes = "" then [] else String.split_on_char '\n' notes in
                Problem { label; message; start; stop; notes; text })
        | "note" -> read "%S" (fun t -> Note t)
        | _ -> read "%S" (fun t -> Output t))
  in
  List.map part (List.filter (( <> ) "") (String.split_on_char '\n' text))
