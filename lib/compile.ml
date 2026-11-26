(* Vastra → OCaml source, for `vastra build`. The input is a session's trace:
   every form the type checker accepted (the prelude, required modules, the
   program), in order. The output links with this library and behaves like
   `vastra run` (or, with [show], like `vastra FILE`).

   Functions defined once become OCaml functions called directly (OCaml then
   does the tail calls); names the program redefines become reference cells,
   so late binding still holds. *)

open Ast

exception Unsupported of string * Reader.span

let p = Printf.sprintf

let mangle s =
  String.concat ""
    (List.map
       (fun c ->
         match c with
         | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' -> String.make 1 c
         | c -> p "_%02x" (Char.code c))
       (List.of_seq (String.to_seq s)))

(* A written type's description, as the program carries it. *)
let shape (s : Shape.t) =
  p "(Marshal.from_string %S 0 : Shape.t)" (Marshal.to_string s [])

let local n = "l_" ^ mangle n
let direct n = "f_" ^ mangle n
let told v = "t" ^ string_of_int v (* a type a generic function is told *)

(* A function generic over number waits for the types it is used at. *)
let generic (fn : expr) code =
  match fn.typed with
  | Generic vars ->
      p "(Value.Generic (function [ %s ] -> %s | _ -> Rt.internal \"wrong number of types\"))"
        (String.concat "; " (List.map told vars))
        code
  | _ -> code

(* Small enough for an int on every target (js_of_ocaml's ints have 32 bits). *)
let z n =
  if Z.numbits n < 31 then p "(Z.of_int (%d))" (Z.to_int n)
  else p "(Z.of_string %S)" (Z.to_string n)

(* A whole number of a known type is a constant; of a type a generic function
   is told, it is made from that type. *)
let literal t n =
  match t with
  | Known Num.Int -> p "(Value.Int %s)" (z n)
  | Known Num.Float -> p "(Value.Float (%h))" (Z.to_float n)
  | Known (Fixed f) -> p "(Value.Fixed (Num.%s, (%ldl)))" (Num.name (Fixed f)) (Num.of_z f n)
  | Hidden v -> p "(Value.literal %s %s)" (told v) (z n)

(* A global's name without its version (see Session.key). *)
let unversioned n = List.hd (String.split_on_char ' ' n)

type global =
  | Direct of int
  (* a function with this many parameters *)
  | Plain
  | Cell

(* How each global is reached in the generated code. *)
let globals entries =
  let counts = Hashtbl.create 64 in
  let add n how =
    Hashtbl.replace counts n
      (match Hashtbl.find_opt counts n with Some _ -> Cell | None -> how)
  in
  List.iter
    (fun (top, _, _) ->
      match top with
      | Def { name; value = { kind = Fn l; _ }; _ } ->
          add name.name (Direct (List.length l.params))
      | Def { name; _ } | Native { name; _ } -> add name.name Plain
      | Ns { name; imports; _ } ->
          List.iter (fun (i : Ast.import) -> add (name ^ "/" ^ i.local) Plain) imports
      | Type { ctors; _ } -> List.iter (fun c -> add c.ctor_name Plain) ctors
      | _ -> ())
    entries;
  (* A name set! changes is a cell. *)
  List.iter
    (fun (top, _, _) ->
      match top with
      | Def { value = e; _ } | Expr e | On { handler = e; _ } ->
          List.iter (fun n -> Hashtbl.replace counts n Cell) (changes e)
      | _ -> ())
    entries;
  counts

(* The globals the program's top-level expressions use, directly or not: only
   these are compiled (macro helpers, for instance, are not needed at run time). *)
let needed entries =
  let bodies = Hashtbl.create 64 in
  List.iter
    (fun (top, _, _) ->
      match top with
      | Def { name; value; _ } -> Hashtbl.add bodies name.name value
      | _ -> ())
    entries;
  let seen = Hashtbl.create 64 in
  let rec visit n =
    if not (Hashtbl.mem seen n) then (
      Hashtbl.add seen n ();
      List.iter (fun v -> List.iter visit (references v)) (Hashtbl.find_all bodies n))
  in
  List.iter
    (fun (top, _, shown) ->
      match top with
      | Expr e when shown -> List.iter visit (references e)
      | On { handler = e; _ } -> List.iter visit (references e)
      | View { place; draw; _ } -> List.iter visit (references place @ references draw)
      (* A definition that runs a task runs, even if nothing uses its name. *)
      | Def { name; value = { kind = Run _; _ }; _ } -> visit name.name
      | _ -> ())
    entries;
  seen

let generate ~show ~js ?(window = false) ?(names = []) ~source entries =
  let how = globals entries in
  let needed = needed entries in
  let used n = Hashtbl.mem needed n in
  let global n =
    match Hashtbl.find_opt how n with
    | Some Cell -> p "!g_%s" (mangle n)
    | _ -> p "g_%s" (mangle n)
  in
  (* A generic function defined once also gets a copy for each number types it
     is used at, where its literals are constants. While a copy is
     compiled, [copying] gives its variables' types. *)
  let generics = Hashtbl.create 16 in
  List.iter
    (fun (top, _, _) ->
      match top with
      | Def { name; value = { kind = Fn l; typed = Generic vars; _ }; _ }
        when Hashtbl.find_opt how name.name <> Some Cell ->
          Hashtbl.replace generics name.name (vars, l)
      | _ -> ())
    entries;
  let copying = ref [] in
  let resolve = function
    | Hidden v when List.mem_assoc v !copying -> Known (List.assoc v !copying)
    | n -> n
  in
  let num n =
    match resolve n with
    | Known (Fixed _ as t) -> p "(Num.Fixed Num.%s)" (Num.name t)
    | Known t -> "Num." ^ Num.name t
    | Hidden v -> told v
  in
  (* The number types a generic name is used at. *)
  let types (e : expr) = match e.typed with Use ns -> List.map num ns | _ -> [] in
  let at (e : expr) code =
    match e.typed with
    | Use ns -> p "(Value.at %s [ %s ])" code (String.concat "; " (List.map num ns))
    | _ -> code
  in
  (* The number of [n]'s copy for the types this use knows, if [n] has copies. *)
  let copies = Hashtbl.create 16 and wanted = Queue.create () in
  let copy (e : expr) n =
    match (Hashtbl.find_opt generics n, e.typed) with
    | Some _, Use ns -> (
        let ts = List.filter_map (fun t -> match resolve t with Known t -> Some t | _ -> None) ns in
        if List.length ts < List.length ns then None
        else
          match Hashtbl.find_opt copies (n, ts) with
          | Some i -> Some i
          | None ->
              let i = Hashtbl.length copies + 1 in
              Hashtbl.add copies (n, ts) i;
              Queue.add (n, ts, i) wanted;
              Some i)
    | _ -> None
  in
  let fresh = ref 0 in
  let rec expr locals (e : expr) =
    let go = expr locals in
    let list items = String.concat "; " (List.map go items) in
    let steps path =
      String.concat "; "
        (List.map
           (function Key (k, _) -> p "Value.Key %S" k | At x -> p "Value.At %s" (go x))
           path)
    in
    match e.kind with
    | Int n | Hex n -> (
        match e.typed with Literal t -> literal (resolve t) n | _ -> p "(Value.Int %s)" (z n))
    | Float f -> p "(Value.Float (%h))" f
    | Bool b -> p "(Value.Bool %b)" b
    | Str s -> p "(Value.Str %S)" s
    | Keyword k -> p "(Value.Keyword %S)" k
    | Var n -> (
        match e.typed with
        | Told_type s -> p "(Json.told %s %s)" (shape s) (global n)
        | _ when List.mem n locals -> at e (local n)
        (* Values, natives and constructors are never generic. *)
        | _ when Hashtbl.find_opt how n = Some Plain -> global n
        | _ -> (
            match copy e n with
            | Some i -> p "g%d_%s" i (mangle n)
            | None -> at e (global n)))
    | Vector items -> p "(Value.Vector [| %s |])" (list items)
    | Record fields ->
        p "(Value.Record [ %s ])"
          (String.concat "; " (List.map (fun (k, v) -> p "(%S, %s)" k (go v)) fields))
    | Get { key; record } -> p "(Rt.get %S %s)" key (go record)
    | Read { target; path } -> p "(Value.get %s [ %s ])" (go target) (steps path)
    | Set { target; path; value } ->
        p "(Value.change ~adds:true %s [ %s ] (fun _ -> %s))" (go target) (steps path)
          (go value)
    | Update { target; path; func } ->
        p
          "(let f = %s in Value.change ~adds:false %s [ %s ] (function Some old -> \
           Rt.apply f [ old ] | None -> Rt.internal \"update added a step\"))"
          (go func) (go target) (steps path)
    | Change { target = { kind = Var n; _ }; value } ->
        p "(g_%s := %s; !Value.changed g_%s; Value.Unit)" (mangle n) (go value) (mangle n)
    | Change _ -> raise (Unsupported ("set! of what is not a name", e.span))
    | Send x -> p "(Value.send %s; Value.Unit)" (go x)
    | Fn l -> generic e (p "(Value.Builtin { builtin_name = \"\"; run = %s })" (lambda locals l))
    (* A local function that calls itself: a generic one is told its
       types first, and then calls itself at those types. *)
    | Let { bindings = [ (b, ({ kind = Fn l; _ } as fn)) ]; body; how = Recursive } ->
        let self = local b.name and locals = b.name :: locals in
        p "(let %s = %s in %s)" self
          (generic fn
             (p "(let rec %s = Value.Builtin { builtin_name = %S; run = %s } in %s)" self
                b.name (lambda locals l) self))
          (expr locals body)
    | Let { bindings; body; _ } ->
        let rec chain locals = function
          | [] -> expr locals body
          | (b, v) :: rest ->
              p "(let %s = %s in %s)" (local b.name) (expr locals v)
                (chain (b.name :: locals) rest)
        in
        chain locals bindings
    (* The bindings run together: Builtins.parallel computes them. *)
    | Par_let { bindings; body } ->
        let case i (_, v) = p "| %d -> %s " i (expr locals v) in
        let name i (b, _) = p "let %s = together.(%d) in " (local b.name) i in
        p
          "(let together = !Builtins.parallel %d (function %s| _ -> Rt.internal \
           \"par/let\") in %s%s)"
          (List.length bindings)
          (String.concat "" (List.mapi case bindings))
          (String.concat "" (List.mapi name bindings))
          (expr (List.map (fun (b, _) -> b.name) bindings @ locals) body)
    | If { condition; then_branch; else_branch } ->
        p "(if Rt.truth %s then %s else %s)" (go condition) (go then_branch)
          (go else_branch)
    | Match { scrutinee; clauses } ->
        let clause (pat, body) =
          let guards = ref [] in
          let pattern = pattern guards pat in
          let guard =
            if !guards = [] then "" else " when " ^ String.concat " && " !guards
          in
          p "| %s%s -> %s" pattern guard
            (expr (Analyze.pattern_vars pat |> List.map fst |> ( @ ) locals) body)
        in
        let scrutinee =
          match e.typed with
          | Decodes s ->
              p "(Json.decode %s %s)" (shape s) (go scrutinee)
          | _ -> go scrutinee
        in
        p "(match %s with %s | _ -> Rt.internal \"no clause matched\")" scrutinee
          (String.concat " " (List.map clause clauses))
    | Call { func = { kind = Var n; _ }; args }
      when Analyze.is_upper n && not (List.mem n locals) ->
        p "(Value.Ctor (%S, [ %s ]))" n (list args)
    | Call { func = { kind = Var n; _ } as func; args }
      when (not (List.mem n locals))
           && Hashtbl.find_opt how n = Some (Direct (List.length args)) -> (
        let args = if args = [] then [ "()" ] else List.map go args in
        match copy func n with
        | Some i -> p "(f%d_%s %s)" i (mangle n) (String.concat " " args)
        | None -> p "(%s %s)" (direct n) (String.concat " " (types func @ args)))
    | Call { func; args } -> p "(Rt.apply %s [ %s ])" (go func) (list args)
    | Quote n ->
        p "(Value.Form (Marshal.from_string %S 0 : Reader.node))" (Marshal.to_string n [])
    | Quasi _ -> raise (Unsupported ("quasiquote in a compiled program", e.span))
    | Await _ -> raise (Unsupported ("@ inside a macro", e.span))
    | Task_of x -> go x
    (* Lift puts Run only at a definition's top, which [statement] compiles. *)
    | Run _ -> raise (Unsupported ("a task run inside a value", e.span))
  and lambda locals l =
    let names = List.map (fun (b : binding) -> b.name) l.params in
    p "(function [ %s ] -> %s | _ -> Rt.internal \"wrong number of arguments\")"
      (String.concat "; " (List.map local names))
      (expr (names @ locals) l.body)
  and pattern guards (pat : pattern) =
    let each ps = String.concat "; " (List.map (pattern guards) ps) in
    match pat.pat with
    | PWild -> "_"
    | PVar n -> local n
    | PInt n ->
        incr fresh;
        let v = p "n%d" !fresh in
        guards := p "Value.is_whole %s %s" (z n) v :: !guards;
        v
    | PStr s -> p "Value.Str %S" s
    | PBool b -> p "Value.Bool %b" b
    | PCtor (n, ps) -> p "Value.Ctor (%S, [ %s ])" n (each ps)
    | PVector ps -> p "Value.Vector [| %s |]" (each ps)
  in
  let say shown text = if show && shown then p "print_endline %S;\n" text else "" in
  let define n value =
    match Hashtbl.find_opt how n with
    | Some Cell -> p "g_%s := %s;\n" (mangle n) value
    | _ -> p "let g_%s = %s in\n" (mangle n) value
  in
  (* A function defined once, called directly as [f] after the types it is
     told, and its value [g], which [wrap] makes wait for those types. *)
  let direct_function ~f ~g ~told ~wrap name (l : lambda) =
    let names = List.map (fun (b : binding) -> b.name) l.params in
    let params =
      String.concat " " (told @ if names = [] then [ "()" ] else List.map local names)
    in
    p "let rec %s %s = %s\nand %s = %s in\n" f params (expr names l.body) g
      (wrap
         (p
            "Value.Builtin { builtin_name = %S; run = (function [ %s ] -> %s %s | _ -> \
             Rt.internal \"wrong number of arguments\") }"
            (unversioned name)
            (String.concat "; " (List.map local names))
            f params))
  in
  (* A top-level task runs, and the lines after it wait for it to end:
     they are what is called when it ends, so each opens a parenthesis. *)
  let waits = ref 0 in
  let statement (top, outcome, shown) =
    let text = Session.outcome_to_string outcome in
    match top with
    | Def { name; value = { kind = Run task; span; _ }; _ } ->
        incr waits;
        (* Spans are in the program's file; a module's has none there. *)
        let span = if shown then span else Diagnostic.nowhere in
        p "Rt.now %s (%d, %d) (fun v ->\n%s" (expr [] task) span.start span.stop
          (define name.name "v")
        ^ say shown text
    | (Def { name; _ } | Native { name; _ }) when not (used name.name) ->
        say shown text
    | Def { name; value = { kind = Fn l; _ } as value; _ }
      when Hashtbl.find_opt how name.name <> Some Cell ->
        let told = match value.typed with Generic vars -> List.map told vars | _ -> [] in
        direct_function ~f:(direct name.name) ~g:("g_" ^ mangle name.name) ~told
          ~wrap:(generic value) name.name l
        ^ say shown text
    | Def { name; value; _ } ->
        let v =
          match value.kind with
          | Fn l ->
              (* Inside its body the function's own name is itself, as in the interpreter. *)
              generic value
                (p "(let rec %s = Value.Builtin { builtin_name = %S; run = %s } in %s)"
                   (local name.name) (unversioned name.name) (lambda [ name.name ] l)
                   (local name.name))
          | _ -> expr [] value
        in
        define name.name v ^ say shown text
    | Native { name; _ } ->
        define name.name (p "(List.assoc %S (Builtins.all @ !Builtins.extra))" name.name)
        ^ say shown text
    | Type { ctors; _ } ->
        String.concat ""
          (List.map
             (fun (c : Ast.ctor) ->
               define c.ctor_name
                 (if c.fields = [] then p "(Value.Ctor (%S, []))" c.ctor_name
                  else p "(Rt.constructor %S)" c.ctor_name)
               ^ Option.fold c.word ~none:"" ~some:(fun w ->
                     p "Hashtbl.replace Value.words %S %S;\n" c.ctor_name w))
             ctors)
        ^ say shown text
    | Expr e ->
        let ty = match outcome with Session.Evaluated { ty; _ } -> ty | _ -> "" in
        if shown then (
          incr waits;
          p "Rt.top %s %S (%d, %d) (fun () ->\n" (expr [] e) ty e.span.start e.span.stop)
        else ""
    (* Handlers and views go to the runtime as they come. *)
    | On { handler; window; _ } ->
        p
          "Value.handlers := !Value.handlers @ [ { Value.from = None; window = %b; \
           handle = %s } ];\n"
          window (expr [] handler)
        ^ say shown text
    | View { place; draw; _ } ->
        p
          "Value.views := !Value.views @ [ { Value.at = None; place = %s; draw = %s } \
           ];\n\
           !Value.redraw ();\n"
          (expr [] place) (expr [] draw)
        ^ say shown text
    | Ns { name; imports; _ } ->
        String.concat ""
          (List.map
             (fun (i : Ast.import) ->
               define (name ^ "/" ^ i.local) (p "(Vastra_web.imported %S)" i.spec))
             imports)
        ^ say shown text
    | Macro _ -> say shown text
  in
  let statements = List.map statement entries in
  (* A copy can ask for copies of other functions, defined before it. *)
  let made = Hashtbl.create 16 in
  while not (Queue.is_empty wanted) do
    let n, ts, i = Queue.pop wanted in
    let vars, l = Hashtbl.find generics n in
    copying := List.combine vars ts;
    Hashtbl.add made n
      (direct_function ~f:(p "f%d_%s" i (mangle n)) ~g:(p "g%d_%s" i (mangle n)) ~told:[]
         ~wrap:Fun.id n l);
    copying := []
  done;
  (* Each function's copies come right after it, before anything uses them. *)
  let statements =
    List.map2
      (fun (top, _, _) code ->
        match top with
        | Def { name; _ } -> code ^ String.concat "" (List.rev (Hashtbl.find_all made name.name))
        | _ -> code)
      entries statements
  in
  let cells =
    Hashtbl.fold
      (fun n h acc ->
        if h = Cell && used n then p "let g_%s = ref Value.Unit in\n" (mangle n) :: acc
        else acc)
      how []
  in
  let imports =
    List.concat_map
      (function
        | Ast.Ns { imports; _ }, _, _ ->
            List.map (fun (i : Ast.import) -> p "%S" i.spec) imports
        | _ -> [])
      entries
  in
  "[@@@warning \"-a\"]\nopen Vastra\n\nlet () =\n"
  ^ (if js then "  Vastra_web.install ();\n" else "")
  ^ (if window then "  Vastra_window.install ();\n" else "")
  ^ "  Rt.show_mode := " ^ string_of_bool show ^ ";\n"
  ^ p "  Rt.source := (%S, %S);\n" (fst source) (snd source)
  ^ p "  Rt.names := [ %s ];\n"
      (String.concat "; " (List.map (fun (n, m) -> p "(%S, %S)" n m) names))
  (* It runs once the ES modules it imports are loaded. *)
  ^ (if js then p "  Vastra_web.preload [ %s ] (fun () ->\n" (String.concat "; " imports)
     else "")
  ^ "  Rt.main "
  (* A page goes on after its last line; Node ends there, its timers too. *)
  ^ (if js then
       "~exit:(fun code -> if code <> 0 || not Vastra_web.in_page then exit code) "
     else "")
  ^ "(fun () ->\n" ^ String.concat "" cells
  ^ String.concat "" statements
  (* What it sent is handled, and a window it opened runs its frames. *)
  ^ "Value.handle_sent ();\n!Value.loop ();\nRt.finish ()" ^ String.make !waits ')'
  ^ (if js then "))\n" else ")\n")

(* Checks the program in [path] like `vastra run` does, and gives its OCaml source
   and the library it links with: a window's links SDL. *)
let program ~show ~js path source =
  let s = Session.create ~base_dir:(Filename.dirname path) ~trace:true () in
  s.check_only <- true;
  (* Like `vastra FILE` when showing results, like `vastra run` otherwise. *)
  s.run_tasks <- not show;
  if js then s.platform <- "js";
  match Session.eval_source ~file:path s source with
  | Error d -> Error d
  | Ok _ -> (
      (* Results show names as typed in the program's file. *)
      let names =
        let env = s.state.env in
        let keys m = List.map fst (Infer.Env.bindings m) in
        List.filter_map
          (fun n ->
            let m = Infer.shown env n in
            if m <> n then Some (n, m) else None)
          (keys env.ctors @ keys env.vars)
      in
      let window = List.mem "vastra.window" s.state.loaded in
      let library =
        if js then "vastra.web" else if window then "vastra.window" else "vastra"
      in
      let entries = List.rev (Option.value s.trace ~default:[]) in
      match generate ~show ~js ~window ~names ~source:(path, source) entries with
      | code -> Ok (code, library)
      | exception Unsupported (what, span) ->
          Error
            (Diagnostic.make ~why:"build" Syntax span
               (what ^ " is not supported by vastra build yet")
            |> Diagnostic.note "run the program with `vastra run` instead"))
