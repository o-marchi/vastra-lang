(* Data → syntax tree: recognises special forms and checks their shape. *)

open Ast

let special_forms =
  [
    "fn";
    "let";
    "par/let";
    "if";
    "match";
    "cond";
    "type";
    "native";
    "get";
    "set";
    "assoc";
    "update";
    "macro";
    "do";
    "later";
    "on";
    "view";
    "set!";
    "update!";
    "send!";
    "ns";
    "quote";
    "quasiquote";
    "await";
    "unquote";
    "unquote-splicing";
  ]

(* Set by the session: which names are macros where the code is analyzed. *)
let is_macro : (string -> bool) ref = ref (fun _ -> false)
let top_level_only =
  [ "type"; "native"; "macro"; "ns"; "on"; "view" ]
(* [why]: the rule's key in why.txt; most syntax errors are a form's shape. *)
let syntax ?(why = "form") span message =
  Diagnostic.make Syntax span message |> Diagnostic.why why

let fail ?why span message = Diagnostic.fail (syntax ?why span message)

let fail_usage ?why span message usage =
  Diagnostic.fail (syntax ?why span message |> Diagnostic.note usage)

(* The fix for clauses from [forms] on, flat ones among them: each
   pattern and the form after it in brackets, the clauses in brackets left as
   they are. None when a pattern has nothing after it. *)
let bracketed (forms : Reader.node list) =
  let rec marks = function
    | [] -> Some []
    | ({ form = Vector (_ :: _ :: _); _ } : Reader.node) :: rest -> marks rest
    | (p : Reader.node) :: (b : Reader.node) :: rest ->
        Option.map (fun m -> (p.span.start, "[") :: (b.span.stop, "]") :: m) (marks rest)
    | [ _ ] -> None
  in
  match (marks forms, forms) with
  | Some m, first :: _ ->
      let last = List.nth forms (List.length forms - 1) in
      let span = { first.span with stop = last.span.stop } in
      let insert text (at, mark) =
        let i = at - span.start in
        String.sub text 0 i ^ mark ^ String.sub text i (String.length text - i)
      in
      let fixed text = Some (List.fold_left insert text (List.rev m)) in
      Some (Diagnostic.Edit (span, fixed))
  | _ -> None

let reserved name = name = "nil" || List.mem name special_forms || !is_macro name

(* Types and constructors start with an uppercase letter, after any module prefix. *)
let is_upper name =
  let base =
    match String.rindex_opt name '/' with
    | Some i -> String.sub name (i + 1) (String.length name - i - 1)
    | None -> name
  in
  base <> "" && base.[0] >= 'A' && base.[0] <= 'Z'

let check_variable name span =
  if name = "nil" then
    Diagnostic.fail
      (syntax ~why:"no-nil" span "there is no `nil` in this language"
      |> Diagnostic.note
           "use Option for a value that may be missing: None or (Some value)");
  if List.mem name special_forms then
    fail ~why:"not-a-value" span
      (Printf.sprintf "`%s` is a special form and cannot be used as a value" name);
  if !is_macro name then
    Diagnostic.fail
      (syntax ~why:"not-a-value" span
        (Printf.sprintf "`%s` is a macro and cannot be used as a value" name)
      |> Diagnostic.note (Printf.sprintf "call it directly, as in (%s ...)" name))

let misplaced_type (node : Reader.node) =
  fail ~why:"written-types" node.span
    "a type is written only on a let's name or a function's parameter"

let binding (node : Reader.node) =
  match node.form with
  | Symbol name when reserved name ->
      let reason =
        if name = "nil" then "there is no nil in this language"
        else if List.mem name special_forms then "it is a special form"
        else "it is a macro"
      in
      fail ~why:"names" node.span
        (Printf.sprintf "`%s` cannot be used as a name: %s" name reason)
  | Symbol name when is_upper name ->
      fail_usage ~why:"names" node.span
        (Printf.sprintf
           "`%s` cannot be used as a name: names starting with an uppercase letter are \
            for types and constructors"
           name)
        "start the name with a lowercase letter"
  | Symbol name -> name_at name node.span
  | List [ { form = Symbol "::"; _ }; _; _ ] -> misplaced_type node
  | _ -> fail node.span "expected a name (a symbol) here"

(* Local names cannot contain '/', so a qualified global name in a macro's
   expansion can never be captured by a local. *)
let local (node : Reader.node) =
  let b = binding node in
  if String.contains b.name '/' && b.name <> "/" then
    fail ~why:"names" node.span
      (Printf.sprintf "`%s` cannot be used as a local name: local names cannot contain /"
         b.name);
  b

(* A let's name or a parameter, with its written type if it has one. *)
let typed (name_of : Reader.node -> binding) (node : Reader.node) =
  match node.form with
  | List [ { form = Symbol "::"; _ }; name; ty ] ->
      { (name_of name) with written = Some ty }
  | _ -> name_of node

let unique what names =
  let seen = Hashtbl.create 8 in
  List.iter
    (fun (name, span) ->
      if Hashtbl.mem seen name then
        fail ~why:"names" span (Printf.sprintf "the %s `%s` appears twice" what name);
      Hashtbl.add seen name ())
    names

let rec pattern (node : Reader.node) =
  let make pat = { pat; pat_span = node.span; written = None } in
  match node.form with
  | Symbol "_" -> make PWild
  | Symbol name when is_upper name -> make (PCtor (name, []))
  | Symbol _ -> make (PVar (local node).name)
  | Int n | Hex n -> make (PInt n)
  | Str s -> make (PStr s)
  | Bool b -> make (PBool b)
  | List ({ form = Symbol name; _ } :: args) when is_upper name ->
      make (PCtor (name, Util.map_in_order pattern args))
  | Vector items -> make (PVector (Util.map_in_order pattern items))
  | Float _ ->
      fail_usage ~why:"patterns" node.span "floats cannot be matched exactly"
        "compare them with < or > instead"
  | _ ->
      fail_usage ~why:"patterns" node.span "this is not a pattern"
        "patterns are _, names, literals, constructors like (Some x), and vectors like \
         [a b]"

(* The name holding the names a branch line changes, when it changes more than
   one: no program can write it, since it has a space. Taking it apart does
   not use it up. *)
let joined_name (form : Reader.node) = Printf.sprintf "changed %d" form.span.start
let joined name = String.starts_with ~prefix:"changed " name

(* What a line run for what it does gives, an @ line's or a set! line's, is
   named so, which no program can write either. *)
let ran = "line ran"

let rec pattern_vars p =
  match p.pat with
  | PVar name -> [ (name, p.pat_span) ]
  | PCtor (_, args) | PVector args -> List.concat_map pattern_vars args
  | _ -> []

(* A call on a line is most often a task that needs its @. *)
let nothing (form : Reader.node) =
  let d =
    syntax ~why:"body-lines" form.span "this line does nothing: its value is not used"
    |> Diagnostic.note
         "a body's last form gives its value; the lines before it name values with let, \
          and change them with set"
  in
  Diagnostic.fail
    (match form.form with
    | List ({ form = Symbol f; _ } :: _) when not (List.mem f special_forms) ->
        Diagnostic.note
          "a task on a line runs with @ before it: @(console/print \"hi\")" d
    | _ -> d)

(* A change that no later line reads does nothing. Infer checks a set line's,
   after what a function holds of it. *)
let unread name span body =
  if not (List.mem name (Ast.references body)) then
    fail_usage ~why:"body-lines" span
      (Printf.sprintf "`%s` is set here but never read after: this line does nothing" name)
      "a change is seen by the lines after it in its body"

let rec analyze (node : Reader.node) : expr =
  let make kind = { kind; span = node.span; origin = node.origin; typed = Untyped } in
  match node.form with
  | Int n -> make (Int n)
  | Hex n -> make (Hex n)
  | Float f -> make (Float f)
  | Bool b -> make (Bool b)
  | Str s -> make (Str s)
  | Symbol name ->
      check_variable name node.span;
      make (Var name)
  | Keyword key -> make (Keyword key)
  | Vector items -> make (Vector (Util.map_in_order analyze items))
  | Map entries -> make (Record (record entries))
  | List [] -> fail node.span "an empty list () cannot be evaluated"
  | List ({ form = Keyword key; _ } :: rest) -> (
      match rest with
      | [ record ] -> make (Get { key; record = analyze record })
      | _ -> fail ~why:"arity" node.span
        (Printf.sprintf "(:%s m) takes exactly one map" key))
  | List ({ form = Symbol "fn"; _ } :: rest) -> make (Fn (fn node.span rest))
  | List ({ form = Symbol "::"; _ } :: _) -> misplaced_type node
  | List ({ form = Symbol "let"; span; _ } :: _) ->
      fail_usage ~why:"body-lines" span
        "let names a value on a line of a body, and gives no value"
        "an expression that needs names is a (do ...): (do (let x 2) (* x x))"
  | List ({ form = Symbol "do"; _ } :: rest) ->
      (* A cond's clause of several lines is a do. *)
      let what = if node.origin = Some "cond" then "clause" else "do" in
      expression_body node.span what [] rest
  | List ({ form = Symbol "later"; _ } :: rest) -> analyze (later node rest)
  | List [ { form = Symbol "send!"; _ }; message ] -> make (Send (analyze message))
  | List ({ form = Symbol "send!"; _ } :: _) ->
      fail_usage node.span "send! takes one message" "for example: (send! (Tick now))"
  | List ({ form = Symbol "par/let"; _ } :: rest) -> make (par_let node.span rest)
  | List ({ form = Symbol "if"; _ } :: rest) -> make (if_ node.span rest)
  | List ({ form = Symbol "match"; _ } :: rest) -> make (match_ node.span rest)
  | List ({ form = Symbol "cond"; _ } :: rest) -> analyze (cond node rest)
  | List [ { form = Symbol "quote"; _ }; x ] -> make (Quote x)
  | List [ { form = Symbol "quasiquote"; _ }; x ] -> make (Quasi (quasi x))
  | List ({ form = Symbol (("quote" | "quasiquote") as q); _ } :: _) ->
      fail ~why:"quasiquote" node.span (Printf.sprintf "%s takes exactly one form" q)
  | List ({ form = Symbol ("unquote" | "unquote-splicing"); _ } :: _) ->
      fail_usage ~why:"quasiquote" node.span
        "~ and ~@ are only allowed inside a quasiquote"
        "for example: `(if ~condition ~then-branch ~else-branch)"
  | List ({ form = Symbol "get"; _ } :: rest) -> (
      match rest with
      | target :: (_ :: _ as steps) ->
          let target = analyze target in
          make (Read { target; path = path steps })
      | [ target ] ->
          fail_usage ~why:"paths" node.span "get needs what to read and a path"
            (Printf.sprintf "without a path, the value is %s itself"
               (Reader.to_source target))
      | [] ->
          fail_usage ~why:"paths" node.span "get needs what to read and a path"
            "for example: (get map :key 0)")
  | List ({ form = Symbol (("set" | "assoc" | "update") as op); _ } :: rest) ->
      change node op rest
  | List ({ form = Symbol (("set!" | "update!") as op); _ } :: rest) -> (
      match rest with
      | ({ form = Symbol _; _ } as n) :: (_ :: _ as more) ->
          let value = new_value node (if op = "set!" then "set" else "update") n more in
          make (Change { target = analyze n; value })
      | _ ->
          fail_usage ~why:"set-names" node.span
            (Printf.sprintf "%s changes one of the file's names: (%s name ...)" op op)
            (Printf.sprintf "for example: (%s count %s)" op
               (if op = "set!" then "0" else "inc")))
  | List [ { form = Symbol "await"; _ }; x ] -> make (Await (analyze x))
  | List ({ form = Symbol "await"; _ } :: _) ->
      fail_usage node.span "@ goes before one task" "for example: @clock/now"
  | List ({ form = Symbol name; span; _ } :: _) when List.mem name top_level_only ->
      fail ~why:"top-level" span
        (Printf.sprintf "%s is only allowed at the top level" name)
  | List (head :: args) ->
      let func = analyze head in
      make (Call { func; args = Util.map_in_order analyze args })

and record entries =
  let seen = Hashtbl.create 8 in
  Util.map_in_order
    (fun ((key : Reader.node), value) ->
      match key.form with
      | Keyword name ->
          if Hashtbl.mem seen name then
            fail ~why:"maps" key.span (Printf.sprintf "duplicate key :%s" name);
          Hashtbl.add seen name ();
          (name, analyze value)
      | _ ->
          fail_usage ~why:"maps" key.span "map keys must be keywords, like :name"
            "for other kinds of keys, use a Dict: (dict/insert key value dict/empty)")
    entries

(* A path: a keyword is a map's key, anything else is computed. *)
and path steps =
  Util.map_in_order
    (fun (s : Reader.node) ->
      match s.form with Keyword k -> Key (k, s.span) | _ -> At (analyze s))
    steps

(* (set value step ... new) and (update value step ... f): the last argument is
   the new value or the function, the others a path. assoc is set. *)
and change node op rest =
  let last = if op = "update" then "a function" else "the new value" in
  match rest with
  | target :: (_ :: _ :: _ as more) ->
      let target = analyze target in
      let steps = List.filteri (fun i _ -> i < List.length more - 1) more in
      let path = path steps in
      let value = analyze (List.nth more (List.length steps)) in
      let kind =
        if op = "update" then Update { target; path; func = value }
        else Set { target; path; value }
      in
      { kind; span = node.span; origin = node.origin; typed = Untyped }
  | _ ->
      fail_usage ~why:"paths" node.span
        (Printf.sprintf "%s needs what to change, a path and %s" op last)
        (Printf.sprintf "for example: (%s map :key %s)" op
           (if op = "update" then "f" else "value"))

and fn span rest =
  let usage = "for example: (fn [params] body)" in
  match rest with
  | [] -> fail_usage span "fn needs a parameter vector and a body" usage
  | { form = Vector params; _ } :: body ->
      let params = Util.map_in_order (typed local) params in
      unique "parameter" (List.map (fun b -> (b.name, b.name_span)) params);
      { params; body = fst (body_of span "fn" (List.map (fun b -> b.name) params) body) }
  | { form = Symbol _; span; _ } :: _ ->
      fail_usage ~why:"top-level" span
        "a named fn defines a function, on a line of its own"
        "for a function value, leave out the name: (fn [x] ...)"
  | params :: _ -> fail_usage params.span "fn expects a parameter vector, like [x]" usage

(* (fn name "doc"? [params] ...), a line defining a function: its
   docstring and the function. *)
and named_fn span rest =
  match docstring rest with
  | _, ({ form = Symbol _; span; _ } : Reader.node) :: _ ->
      fail_usage span "fn expects a parameter vector, like [x]"
        "for example: (fn name [params] body)"
  | doc, rest -> (doc, fn span rest)

and docstring = function
  | ({ form = Str d; _ } : Reader.node) :: (_ :: _ as rest) -> (Some d, rest)
  | rest -> (None, rest)

(* A body: lines, then its last form, which gives its value. [own]: the
   names it starts with, a function's parameters. Also gives the names it
   changes that it does not define. *)
and body_of span what own forms =
  match List.rev forms with
  | [] -> fail span (Printf.sprintf "%s needs a body" what)
  | last :: before ->
      let wrap, changed = lines own (List.rev before) in
      (wrap (analyze last), List.filter (( <> ) ran) changed)

(* A body that gives a value, a do's or a clause's: a change to a name it
   doesn't own would end with it. *)
and expression_body span what own forms =
  match body_of span what own forms with
  | e, [] -> e
  | _, n :: _ ->
      fail_usage ~why:"body-lines" span
        (Printf.sprintf "this %s changes `%s`, which is not its own name" what n)
        (Printf.sprintf
           "a %s gives a value, and the change would end with it: name a new value \
            with let instead"
           what)

(* Lines, as what they wrap around the rest of their body, and the names they
   change that the body does not define, in order. A name changed here
   counts as the body's from then on, so a later let of it is refused. *)
and lines own = function
  | [] -> (Fun.id, [])
  | form :: more ->
      let wrap, defined, changed = line own form in
      let changed = List.filter (fun n -> not (List.mem n own)) changed in
      let rest, later = lines (defined @ changed @ own) more in
      ((fun body -> wrap (rest body)), merge changed later)

and merge names more = names @ List.filter (fun n -> not (List.mem n names)) more

(* A line: what it wraps around the rest of the body, the names it defines,
   and those it changes, [ran] among them if it acts. *)
and line own (form : Reader.node) =
  let made kind = { kind; span = form.span; origin = form.origin; typed = Untyped } in
  let named ?(how = Names) b value body =
    made (Let { bindings = [ (b, value) ]; body; how })
  in
  (* _ names what isn't wanted: it is never one of the body's names. *)
  let defines (b : binding) = if b.name = "_" then [] else [ b.name ] in
  let fresh (b : binding) =
    if List.mem b.name own && b.name <> "_" then
      fail_usage ~why:"body-lines" b.name_span
        (Printf.sprintf "`%s` is already named in this body" b.name)
        (Printf.sprintf "to change it, write (set %s value)" b.name)
  in
  match form.form with
  | List ({ form = Symbol "let"; _ } :: rest) -> (
      match rest with
      | [ n; value ] ->
          let b = typed local n in
          fresh b;
          (named b (analyze value), defines b, [])
      | n :: value :: (_ :: _ as clauses) ->
          let b = typed local n in
          fresh b;
          (failing form b value clauses, defines b, [])
      | _ ->
          fail_usage form.span "let needs a name and a value" "for example: (let width 16)")
  | List
      ({ form = Symbol "fn"; _ }
      :: ({ form = Symbol _ | List [ { form = Symbol "::"; _ }; _; _ ]; _ } as n)
      :: rest) ->
      let b = local n in
      fresh b;
      (named ~how:Recursive b (made (Fn (snd (named_fn form.span rest)))), [ b.name ], [])
  | List
      ({ form = Symbol (("set" | "update") as op); _ }
      :: ({ form = Symbol _; _ } as n) :: (_ :: _ as rest)) ->
      let b = local n in
      (named ~how:Changes b (new_value form op n rest), [], [ b.name ])
  | List ({ form = Symbol (("set" | "update") as op); _ } :: _) ->
      fail_usage ~why:"set-names" form.span
        (Printf.sprintf "%s as a line changes a name: (%s name ...)" op op)
        (Printf.sprintf "for example: (%s count %s)" op
           (if op = "set" then "0" else "inc"))
  | List ({ form = Symbol ("if" | "cond" | "match" | "do"); _ } :: _) -> branch_line form
  (* A line that changes the file's names: a set!, or a call of a !
     function; or one that runs a task and goes on when it ends. *)
  | List [ { form = Symbol "await"; _ }; _ ] | List ({ form = Symbol "later"; _ } :: _) ->
      (named (name_at ran form.span) (analyze form), [], [ ran ])
  | List ({ form = Symbol f; _ } :: _) when String.ends_with ~suffix:"!" f ->
      (named (name_at ran form.span) (analyze form), [], [ ran ])
  | _ -> nothing form

(* The new value a change gives the name [n]: set's, from a value, or
   update's, from a function of the old one, with or without a path. *)
and new_value (form : Reader.node) op (n : Reader.node) rest =
  match rest with
  | [ value ] when op = "set" -> analyze value
  | [ f ] ->
      let call = Call { func = analyze f; args = [ analyze n ] } in
      { kind = call; span = form.span; origin = form.origin; typed = Untyped }
  | _ -> change form op (n :: rest)

(* (let name value clause ...): the name gets what the value gives when
   it succeeds, a task behind @, a Result or an Option, and the clauses take
   the failure, as a match's do. A clause gives the body's value. *)
and failing (form : Reader.node) b (value : Reader.node) clauses =
  let node f = { value with form = f } in
  let success = ref "Ok" in
  let clause span (p : pattern) lines =
    (match p.pat with
    | PCtor ("Err", [ _ ]) -> ()
    | PCtor ("None", []) -> success := "Some"
    | _ ->
        fail_usage ~why:"let-clauses" p.pat_span
          "a clause of let takes a failure: (Err pattern) or None"
          "the name gets what succeeds; the clauses say what happens otherwise");
    expression_body span "clause" (List.map fst (pattern_vars p)) lines
  in
  (* A task's failure is a value, matched like a Result's. *)
  let value =
    match value.form with
    | List [ ({ form = Symbol "await"; _ } as at); task ] ->
        node (List [ at; node (List [ node (Symbol "task/to-result"); task ]) ])
    | _ -> value
  in
  let scrutinee, clauses = match_parts "let" form.span (value :: clauses) clause in
  let pat = if b.name = "_" then PWild else PVar b.name in
  let name = { pat; pat_span = b.name_span; written = b.written } in
  let succeeds =
    { pat = PCtor (!success, [ name ]); pat_span = b.name_span; written = None }
  in
  fun body ->
    let kind = Match { scrutinee; clauses = (succeeds, body) :: clauses } in
    { kind; span = form.span; origin = Some "let"; typed = Untyped }

(* (later task clause ...): starts the task, and goes on at once. When it
   ends, its outcome meets the clauses, a match's, in a task of their own.
   Without clauses, the checker makes sure the task cannot fail. *)
and later (node : Reader.node) rest =
  let made form = { node with form; origin = Some "later" } in
  let s name = made (Symbol name) and l items = made (List items) in
  match rest with
  | [ task ] -> l [ s "await"; l [ s "macro/later-dropping"; task ] ]
  | task :: (_ :: _ as clauses) ->
      (* Checked here, so that an error names later, not the match it makes. *)
      ignore (clauses_of "later" clauses);
      (* No program can write this name: it has a space. The @ line makes the
         clauses a task, whether they wait or not. *)
      let outcome = s "later outcome" in
      let handler =
        l
          [
            s "fn";
            made (Vector [ outcome ]);
            l [ s "await"; l [ s "task/succeed"; made (Bool true) ] ];
            l (s "match" :: outcome :: clauses);
          ]
      in
      l [ s "await"; l [ s "macro/later"; task; handler ] ]
  | _ ->
      fail_usage ~why:"later" node.span "later needs a task, and clauses for how it ends"
        "for example: (later (http/get-text url) [(Ok text) ...] [(Err e) ...])"

(* An if, cond, match or do line: a set in a branch changes the name for the
   rest of the body. A branch is lines, or unit for none. *)
and branch_line (form : Reader.node) =
  let branch own (forms : Reader.node list) =
    match forms with
    | [ { form = Symbol "unit"; _ } ] -> (Fun.id, [])
    | [ { form = List ({ form = Symbol "do"; _ } :: (_ :: _ as forms)); _ } ] | forms ->
        lines own forms
  in
  match form.form with
  | List ({ form = Symbol "if"; _ } :: rest) ->
      let condition, t, e = if_parts form.span rest (fun n -> branch [] [ n ]) in
      join form [ t; e ] (fun value ->
          let then_branch = fst t (value ()) in
          If { condition; then_branch; else_branch = fst e (value ()) })
  | List ({ form = Symbol "cond"; _ } :: rest) -> branch_line (cond form rest)
  | List ({ form = Symbol "match"; _ } :: rest) ->
      let scrutinee, clauses =
        match_parts "match" form.span rest (fun _ p ->
            branch (List.map fst (pattern_vars p)))
      in
      join form (List.map snd clauses) (fun value ->
          let clause (p, (wrap, _)) = (p, wrap (value ())) in
          Match { scrutinee; clauses = List.map clause clauses })
  | List ({ form = Symbol "do"; _ } :: forms) ->
      if forms = [] then fail form.span "do needs a body";
      let b = lines [] forms in
      join form [ b ] (fun value -> (fst b (value ())).kind)
  | _ -> nothing form

(* The names the branches of a line change: each branch gives them as its
   [value], one name as itself and more in a map, and they are named again
   after the line. A line whose branches only act gives unit. *)
and join (form : Reader.node) branches build =
  let names = List.fold_left (fun names (_, more) -> merge names more) [] branches in
  let acts = List.mem ran names in
  let names = List.filter (( <> ) ran) names in
  if names = [] && not acts then nothing form;
  let made kind = { kind; span = form.span; origin = form.origin; typed = Untyped } in
  let var n = made (Var n) in
  let value () =
    match names with
    | [] -> var "unit"
    | [ n ] -> var n
    | _ -> made (Record (List.map (fun n -> (n, var n)) names))
  in
  let joined = made (build value) in
  let named bindings body =
    let bind (n, v) = (name_at n form.span, v) in
    made (Let { bindings = List.map bind bindings; body; how = Names })
  in
  let wrap body =
    List.iter (fun n -> unread n form.span body) names;
    match names with
    | [] -> named [ (ran, joined) ] body
    | [ n ] -> named [ (n, joined) ] body
    | _ ->
        let all = joined_name form in
        let part n = (n, made (Get { key = n; record = var all })) in
        named [ (all, joined) ] (named (List.map part names) body)
  in
  (wrap, [], if acts then names @ [ ran ] else names)

(* (par/let [a (f x) b (g y)] body): the bindings run together, so none
   can use another; Lift refuses one that waits for a task. *)
and par_let span rest =
  let usage = "for example: (par/let [a (f x) b (g y)] (+ a b))" in
  let bindings, body =
    match rest with
    | [] -> fail_usage ~why:"parallel" span
      "par/let needs a binding vector and a body" usage
    | ({ form = Vector parts; _ } as v) :: body ->
        if List.length parts mod 2 <> 0 then
          fail_usage ~why:"parallel" v.span
            "par/let bindings must come in name/value pairs" usage;
        let rec pairs = function
          | n :: value :: rest ->
              let b = typed local n in
              let v = analyze value in
              (b, v) :: pairs rest
          | _ -> []
        in
        let bindings = pairs parts in
        (bindings, single_body span "par/let" body)
    | v :: _ ->
        fail_usage ~why:"parallel" v.span
          "par/let expects a binding vector, like [name value]" usage
  in
  unique "binding" (List.map (fun (b, _) -> (b.name, b.name_span)) bindings);
  List.iter
    (fun (b, v) ->
      let uses = Ast.references v in
      let other (o, _) = o.name <> b.name && List.mem o.name uses in
      match List.find_opt other bindings with
      | Some (o, _) ->
          Diagnostic.fail
            (syntax ~why:"parallel" v.span
               (Printf.sprintf "`%s` cannot use `%s`: the bindings of par/let run together"
                  b.name o.name)
            |> Diagnostic.note
                 (Printf.sprintf "to use it, bind `%s` in a let around the par/let"
                    o.name))
      | None -> ())
    bindings;
  Par_let { bindings; body }

and if_ span rest =
  let condition, then_branch, else_branch = if_parts span rest analyze in
  If { condition; then_branch; else_branch }

and if_parts : 'a. span -> Reader.node list -> (Reader.node -> 'a) -> expr * 'a * 'a =
 fun span rest branch ->
  match rest with
  | [ c; t; e ] ->
      let condition = analyze c in
      let t = branch t in
      (condition, t, branch e)
  | [ _; _ ] ->
      fail_usage ~why:"no-nil" span "if needs an else branch"
        "there is no nil, so both branches must produce a value"
  | _ ->
      fail_usage span "if expects a condition, a then branch and an else branch"
        "for example: (if condition then else)"

and match_ span rest =
  let scrutinee, clauses =
    match_parts "match" span rest (fun span p lines ->
        expression_body span "clause" (List.map fst (pattern_vars p)) lines)
  in
  Match { scrutinee; clauses }

(* The value matched, and each clause's pattern with its [result], from the
   clause's span, pattern and lines. [what]: the form written. *)
and match_parts :
      'a.
      string ->
      span ->
      Reader.node list ->
      (span -> pattern -> Reader.node list -> 'a) ->
      expr * (pattern * 'a) list =
 fun what span rest result ->
  match rest with
  | [] | [ _ ] ->
      fail_usage span "match needs a value and at least one clause"
        "for example: (match shape [(Circle r) (* r r)] [Square 1])"
  | scrutinee :: clauses ->
      let clauses = clauses_of what clauses in
      let scrutinee = analyze scrutinee in
      let clause ((c : Reader.node), p, lines) =
        let p = pattern p in
        unique "name" (pattern_vars p);
        (p, result c.span p lines)
      in
      (scrutinee, Util.map_in_order clause clauses)

(* The clauses of a match, cond, let or later, each [pattern line ...]:
   the clause, its pattern and its lines. A flat pair's fix is the pair in
   brackets. *)
and clauses_of what (forms : Reader.node list) =
  let head = if what = "cond" then "test" else "pattern" in
  let rec go = function
    | [] -> []
    | ({ form = Vector (p :: (_ :: _ as lines)); _ } as c : Reader.node) :: rest ->
        (c, p, lines) :: go rest
    | { form = Vector _; span; _ } :: _ ->
        fail ~why:"clauses" span
          (Printf.sprintf "a clause of %s needs a %s and its lines: [%s line ...]" what
             head head)
    | p :: rest ->
        let pair =
          match rest with b :: _ -> { p.span with stop = b.span.stop } | [] -> p.span
        in
        let d =
          syntax ~why:"clauses" pair
            (Printf.sprintf "a clause of %s goes in brackets: [%s line ...]" what head)
        in
        (* A macro may have made it from a clause: html, an element. *)
        let made m = Diagnostic.note (Printf.sprintf "in this use of `%s`" m) d in
        let d = Option.fold p.origin ~none:d ~some:made in
        let fixed f = Diagnostic.fix f d in
        Diagnostic.fail (Option.fold (bracketed (p :: rest)) ~none:d ~some:fixed)
  in
  go forms

(* (cond [test line ...] ... [_ line ...]) is the ifs it stands for,
   each spanning the whole cond. *)
and cond (node : Reader.node) rest =
  let made form = { node with form; origin = Some "cond" } in
  let body (c : Reader.node) = function
    | [ line ] -> line
    | lines ->
        let do_ = { c with form = Symbol "do" } in
        { c with form = List (do_ :: lines); origin = Some "cond" }
  in
  let rec ifs = function
    | [ (c, ({ form = Symbol "_"; _ } : Reader.node), lines) ] -> body c lines
    | (_, { form = Symbol "_"; span; _ }, _) :: _ ->
        fail_usage ~why:"clauses" span "`_` can only be the last test of a cond"
          "for example: (cond [(< n 0) \"below\"] [_ \"not below\"])"
    (* As in Clojure, but inside html a [:keyword ...] is an element. *)
    | (_, { form = Keyword "else"; span; _ }, _) :: _ ->
        Diagnostic.fail
          (syntax ~why:"clauses" span "a cond ends with [_ ...], not [:else ...]"
          |> Diagnostic.note "`_` takes what no test before it took, as in a match"
          |> Diagnostic.fix (Edit (span, fun _ -> Some "_")))
    | (c, test, lines) :: more ->
        made (List [ made (Symbol "if"); test; body c lines; ifs more ])
    | [] ->
        fail_usage ~why:"no-nil" node.span "cond needs a [_ ...] clause at the end"
          "there is no nil to give when no test holds"
  in
  ifs (clauses_of "cond" rest)

and quasi (n : Reader.node) =
  match n.form with
  | List [ { form = Symbol "unquote"; _ }; e ] -> Unquote (analyze e)
  | List [ { form = Symbol "unquote-splicing"; _ }; _ ] ->
      fail ~why:"quasiquote" n.span "~@ is only allowed inside a list or a vector"
  | Symbol s when String.length s > 1 && String.ends_with ~suffix:"#" s ->
      Gensym (String.sub s 0 (String.length s - 1))
  | List items -> Coll (CList, List.map item items)
  | Vector items -> Coll (CVector, List.map item items)
  | Map entries -> Coll (CMap, List.concat_map (fun (k, v) -> [ item k; item v ]) entries)
  | _ -> Leaf n

and item (n : Reader.node) =
  match n.form with
  | List [ { form = Symbol "unquote-splicing"; _ }; e ] -> Splice (analyze e)
  | _ -> Item (quasi n)

and single_body span what = function
  | [] -> fail ~why:"parallel" span (Printf.sprintf "%s needs a body" what)
  | [ body ] -> analyze body
  | _ :: (extra : Reader.node) :: _ ->
      Diagnostic.fail
        (syntax ~why:"parallel" extra.span
          (Printf.sprintf "a %s body is one expression" what)
        |> Diagnostic.note
             "lines go in a do: (par/let [a (f x) b (g y)] (do (let c (+ a b)) (* c c)))")

(* The core's operators, which take two or more arguments in a call,
   task/race, which races two or more tasks written out, and range, which
   counts from 0 when given one. *)
let operators = [ "+"; "-"; "*"; "/"; "min"; "max"; "task/race"; "range" ]

(* A call to one of them, once names are resolved, so that a local or a
   module's own + is called as written. More arguments fold left, so
   (+ a b c) rounds as C's a + b + c, (- x) negates, and (range n) is
   (range 0 n). The calls made span the one written and say they come from the
   operator, so errors name it. *)
let operator op (e : expr) =
  match e.kind with
  | Call { func; args } -> (
      let func = { func with origin = Some (Option.value func.origin ~default:op) } in
      let call func args = { e with kind = Call { func; args } } in
      match args with
      | [ _; _ ] -> e
      | [ x ] when op = "-" -> call { func with kind = Var "macro/negate" } [ x ]
      | [ n ] when op = "range" ->
          let zero = { n with kind = Int Z.zero; span = func.span; origin = Some op } in
          call func [ zero; n ]
      | a :: b :: more when op <> "range" ->
          List.fold_left (fun left x -> call func [ left; x ]) (call func [ a; b ]) more
      | _ ->
          fail ~why:"arity" e.span
            (Printf.sprintf "`%s` takes %s, but was given %d" op
               (match op with
               | "-" -> "one or more arguments"
               | "range" -> "one or two arguments"
               | _ -> "two or more arguments")
               (List.length args)))
  | _ -> e

let type_name (node : Reader.node) =
  match node.form with
  | Symbol name when is_upper name -> name_at name node.span
  | _ ->
      fail_usage node.span "a type name must start with an uppercase letter"
        "for example: (type Shape ...)"

let type_def (node : Reader.node) (rest : Reader.node list) =
  let usage = "for example: (type (Option a) None (Some a))" in
  let name, params, ctors =
    match rest with
    | [] -> fail_usage node.span "type needs a name" usage
    | { form = List (name :: params); _ } :: ctors ->
        (type_name name, Util.map_in_order binding params, ctors)
    | name :: ctors -> (type_name name, [], ctors)
  in
  unique "type parameter" (List.map (fun b -> (b.name, b.name_span)) params);
  (* (type Person {...}) names a map type. *)
  let shape, ctors =
    match ctors with [ ({ form = Map _; _ } as m) ] -> (Some m, []) | _ -> (None, ctors)
  in
  let ctor (c : Reader.node) =
    let make head fields =
      { ctor_name = (type_name head).name; fields; ctor_span = c.span; word = None }
    in
    match c.form with
    | Symbol _ -> make c []
    | List (head :: fields) -> make head fields
    | _ ->
        fail_usage c.span "a constructor is a name, or a list of a name and field types"
          usage
  in
  (* A constructor's outside word follows it: Female "female". *)
  let rec ctors_of = function
    | c :: { Reader.form = Str w; _ } :: rest ->
        let c = ctor c in
        { c with word = Some w } :: ctors_of rest
    | c :: rest ->
        let c = ctor c in
        c :: ctors_of rest
    | [] -> []
  in
  let ctors = ctors_of ctors in
  unique "constructor" (List.map (fun c -> (c.ctor_name, c.ctor_span)) ctors);
  unique "outside word"
    (List.filter_map (fun c -> Option.map (fun w -> (w, c.ctor_span)) c.word) ctors);
  Type { name; params; ctors; shape }

(* (macro name "doc"? [params & rest] body) *)
(* A macro's name: like any binding, except that it may already be a macro
   (redefining one in the REPL). *)
let macro_name (node : Reader.node) =
  let saved = !is_macro in
  (is_macro := fun _ -> false);
  Fun.protect ~finally:(fun () -> is_macro := saved) (fun () -> binding node)

let macro (node : Reader.node) (rest : Reader.node list) =
  let usage =
    "for example: (macro unless [condition then else] `(if ~condition ~else ~then))"
  in
  let name, rest =
    match rest with
    | n :: r -> (macro_name n, r)
    | [] -> fail_usage node.span "macro needs a name" usage
  in
  let doc, rest = docstring rest in
  match rest with
  | { form = Vector ps; _ } :: body ->
      let rec params = function
        | [] -> ([], None)
        | [ ({ form = Symbol "&"; _ } : Reader.node); r ] -> ([], Some (local r))
        | ({ form = Symbol "&"; span; _ } : Reader.node) :: _ ->
            fail span "& must be followed by exactly one name"
        | p :: more ->
            let p = local p in
            let ps, r = params more in
            (p :: ps, r)
      in
      let params, rest_param = params ps in
      let all = params @ Option.to_list rest_param in
      unique "parameter" (List.map (fun b -> (b.name, b.name_span)) all);
      let body = fst (body_of node.span "macro" (List.map (fun b -> b.name) all) body) in
      Macro { name; doc; params; rest = rest_param; body }
  | _ -> fail_usage node.span "macro needs a parameter vector and a body" usage

(* (on pattern ...): a handler, the function that, given an event,
   gives (Some run) where run runs the body if the event matches, else None.
   Code made here says it comes from on: the body is top-level code. *)
let handler (node : Reader.node) (pattern_node : Reader.node) body =
  let p = pattern pattern_node in
  unique "name" (pattern_vars p);
  let made kind = { kind; span = node.span; origin = Some "on"; typed = Untyped } in
  let run = fst (body_of node.span "on" (List.map fst (pattern_vars p)) body) in
  let thunk = made (Fn { params = []; body = run }) in
  let some = made (Call { func = made (Var "Some"); args = [ thunk ] }) in
  let rest =
    match p.pat with
    | PWild | PVar _ -> []
    | _ -> [ ({ pat = PWild; pat_span = node.span; written = None }, made (Var "None")) ]
  in
  (* No program can write this name: it has a space. *)
  let event = name_at "on event" node.span in
  let scrutinee = made (Var event.name) in
  let body = made (Match { scrutinee; clauses = (p, some) :: rest }) in
  let waits = Lift.first_await run <> None in
  let handler = made (Fn { params = [ event ]; body }) in
  On { handler; shown = Reader.to_source pattern_node; window = false; waits }

(* (view place ...): what is shown at the place, as (fn [] body). *)
let view (node : Reader.node) (place : Reader.node) body =
  let draw = Fn { params = []; body = fst (body_of node.span "view" [] body) } in
  View
    {
      place = analyze place;
      draw = { kind = draw; span = node.span; origin = Some "view"; typed = Untyped };
      shown = Reader.to_source place;
    }

(* (ns name "doc"? (:require [module :as alias :refer [names]] ...)) *)
let ns (node : Reader.node) (rest : Reader.node list) =
  let usage = "for example: (ns my-app (:require [vastra.file :as file]))" in
  let name, rest =
    match rest with
    | { form = Symbol n; _ } :: r -> (n, r)
    | _ -> fail_usage ~why:"modules" node.span "ns needs a module name" usage
  in
  let rest = match rest with { form = Str _; _ } :: r -> r | r -> r in
  let require (spec : Reader.node) =
    let rec options r = function
      | ({ form = Keyword "as"; _ } : Reader.node) :: { form = Symbol a; _ } :: more ->
          options { r with alias = Some a } more
      | { form = Keyword "refer"; _ } :: { form = Vector names; _ } :: more ->
          let name (n : Reader.node) =
            match n.form with
            | Symbol s -> s
            | _ -> fail ~why:"modules" n.span "expected a name to refer"
          in
          options { r with refer = r.refer @ List.map name names } more
      | [] -> r
      | (other : Reader.node) :: _ ->
          fail_usage ~why:"modules" other.span
            "expected :as alias or :refer [names]" usage
    in
    match spec.form with
    | Vector ({ form = Symbol m; _ } :: opts) ->
        options { module_ = m; alias = None; refer = []; at = spec.span } opts
    | Symbol m -> { module_ = m; alias = None; refer = []; at = spec.span }
    | _ -> fail_usage ~why:"modules" spec.span "expected [module :as alias]" usage
  in
  let import (node : Reader.node) : import =
    match node.form with
    | Vector [ { form = Symbol local; _ }; { form = Str spec; _ } ] ->
        { local; spec; import_at = node.span }
    | _ ->
        fail_usage ~why:"modules" node.span
          "expected [name \"module\"]" "for example: [dayjs \"dayjs\"]"
  in
  let clause (requires, targets, imports) (c : Reader.node) =
    match c.form with
    | List ({ form = Keyword "require"; _ } :: specs) ->
        (requires @ List.map require specs, targets, imports)
    | List ({ form = Keyword "target"; _ } :: ts) ->
        let target (t : Reader.node) =
          match t.form with
          | Keyword k -> k
          | _ -> fail_usage ~why:"modules" t.span "a target is a keyword, like :js" usage
        in
        (requires, targets @ List.map target ts, imports)
    | List ({ form = Keyword "import"; _ } :: specs) ->
        (requires, targets, imports @ List.map import specs)
    | _ ->
        fail_usage ~why:"modules" c.span
          "expected (:require ...), (:target ...) or (:import ...)" usage
  in
  let requires, targets, imports = List.fold_left clause ([], [], []) rest in
  Ns { name; requires; targets; imports }

let analyze_top ~trusted (node : Reader.node) =
  match node.form with
  | List ({ form = Symbol "let"; _ } :: rest) -> (
      let def name doc value =
        Def { name = typed binding name; doc; value = analyze value }
      in
      match rest with
      | [ name; value ] -> def name None value
      | [ name; { form = Str doc; _ }; value ] -> def name (Some doc) value
      | _ :: _ :: _ :: _ ->
          fail_usage ~why:"let-clauses" node.span
            "a let's clause ends a function or a handler, and the top of a file is \
             neither"
            "for example, in a function: \
             (fn age [text] (let a (parse-age text) [(Err why) 0]) a)"
      | _ ->
          fail_usage node.span "let needs a name and a value" "for example: (let name value)")
  | List
      ({ form = Symbol "fn"; _ }
      :: ({ form = Symbol _ | List [ { form = Symbol "::"; _ }; _; _ ]; _ } as name)
      :: rest) ->
      let name = binding name in
      let doc, l = named_fn node.span rest in
      let fn = { kind = Fn l; span = node.span; origin = node.origin; typed = Untyped } in
      Def { name; doc; value = fn }
  | List ({ form = Symbol "on"; _ } :: pattern :: (_ :: _ as body)) ->
      handler node pattern body
  | List ({ form = Symbol "on"; _ } :: _) ->
      fail_usage node.span "on needs a pattern and a body"
        "for example: (on Increment (set! total (inc total)))"
  | List ({ form = Symbol "view"; _ } :: place :: (_ :: _ as body)) ->
      view node place body
  | List ({ form = Symbol "view"; _ } :: _) ->
      fail_usage node.span "view needs a place and a body"
        "for example: (view \"#app\" (html [:p \"hello\"]))"
  | List ({ form = Symbol "type"; _ } :: rest) -> type_def node rest
  | List ({ form = Symbol "macro"; _ } :: rest) -> macro node rest
  | List ({ form = Symbol "ns"; _ } :: rest) -> ns node rest
  | List ({ form = Symbol "native"; _ } :: rest) -> (
      if not trusted then
        fail ~why:"top-level" node.span
          "native declarations are only allowed in the prelude";
      match rest with
      | [ { form = Symbol name; span; _ }; ty ] ->
          Native { name = name_at name span; ty }
      | _ -> fail node.span "native needs a name and a type")
  | _ -> Expr (analyze node)
