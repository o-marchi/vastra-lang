type span = Reader.span

(* [name] without the ! at its end. *)
let unbang name = String.sub name 0 (String.length name - 1)

(* [written]: the type written on a name, name::Type, as the checker reads it. *)
type binding = { name : string; name_span : span; written : Reader.node option }

let name_at name name_span = { name; name_span; written = None }

(* A let's name is a pattern when the let has failure clauses. *)
type pattern = { pat : pat; pat_span : span; written : Reader.node option }

and pat =
  | PWild
  | PVar of string
  | PInt of Z.t
  | PStr of string
  | PBool of bool
  | PCtor of string * pattern list
  | PVector of pattern list

(* [origin]: the macro this expression was expanded from, if any. [typed]: what
   the checker tells the code that runs about it. *)
type expr = { kind : kind; span : span; origin : string option; mutable typed : typed }

(* The number types running code needs. *)
and typed =
  | Untyped
  | Literal of num (* a whole number of this type *)
  | Use of num list (* a name generic over number, used at these types *)
  | Generic of int list (* a function told the types of these number variables *)
  | Decodes of Shape.t (* a let decoding a Json value by its written type *)
  | Told_type of Shape.t (* a native told the written type of what it gives *)
  | Type of Types.t (* any other expression's type, for a printer that needs it *)

(* [Hidden v]: the type an enclosing generic function is told for its variable v. *)
and num = Known of Num.t | Hidden of int

and kind =
  | Int of Z.t
  | Hex of Z.t (* any whole-number type, never a Float *)
  | Float of float
  | Bool of bool
  | Str of string
  | Var of string
  | Keyword of string
  | Vector of expr list
  | Record of (string * expr) list
  | Get of { key : string; record : expr }
  | Read of { target : expr; path : step list } (* (get target step ...) *)
  | Set of { target : expr; path : step list; value : expr }
  | Update of { target : expr; path : step list; func : expr }
  | Change of { target : expr; value : expr }
    (* set! or update!: the file's name [target] gets [value] *)
  | Send of expr (* send!: a message of the file's, handled after the current one *)
  | Fn of lambda
  | Let of { bindings : (binding * expr) list; body : expr; how : how }
  | Par_let of { bindings : (binding * expr) list; body : expr }
    (* the bindings run together: none uses another or waits for a task *)
  | If of { condition : expr; then_branch : expr; else_branch : expr }
  | Match of { scrutinee : expr; clauses : (pattern * expr) list }
  | Call of { func : expr; args : expr list }
  | Quote of Reader.node
  | Quasi of quasi
  | Await of expr (* @x, until Lift pulls it out *)
  | Task_of of expr (* after Lift: the task for x, a task *)
  | Run of expr (* after Lift, a definition's value: run the task when defining *)

(* A quasiquote template: code with holes filled when it is evaluated. *)
and quasi =
  | Leaf of Reader.node
  | Gensym of string (* x# : a fresh name per evaluation *)
  | Unquote of expr
  | Coll of coll * item list

(* A step of a path in get, set and update: a map's key, written as a
   keyword, or a vector's index or a dictionary's key, computed. *)
and step = Key of string * span | At of expr
and item = Item of quasi | Splice of expr
and coll = CList | CVector | CMap
and lambda = { params : binding list; body : expr }

(* How a let names: a value; a set or update line, changing a name and
   keeping its type; or a named fn line, a function that can call itself. *)
and how = Names | Changes | Recursive

(* Types and constructor fields stay as reader nodes; the checker reads them. *)
type ctor = {
  ctor_name : string;
  fields : Reader.node list;
  ctor_span : span;
  word : string option; (* what it is called outside, in data *)
}

type top =
  | Def of { name : binding; doc : string option; value : expr }
  | Expr of expr
  | Type of {
      name : binding;
      params : binding list;
      ctors : ctor list;
      shape : Reader.node option; (* the map type it names instead *)
    }
  | Native of { name : binding; ty : Reader.node }
  | Macro of {
      name : binding;
      doc : string option;
      params : binding list;
      rest : binding option;
      body : expr;
    }
  | On of { handler : expr; shown : string; window : bool; waits : bool }
    (* a handler, as (fn [event] (match event pattern (Some (fn [] body)) _ None)):
       [shown], its pattern as written; [window], whether it takes window events;
       [waits], whether its body has an @ *)
  | View of { place : expr; draw : expr; shown : string }
    (* what is shown at [place], drawn again after every change by
       [draw], (fn [] body); [shown], the place as written *)
  | Ns of {
      name : string;
      requires : require list;
      targets : string list;
      imports : import list;
    }

and require = { module_ : string; alias : string option; refer : string list; at : span }

(* An ES module, named [local] in the module that imports it. *)
and import = { local : string; spec : string; import_at : span }

(* The expressions directly inside [e]. *)
let children e =
  let steps = List.filter_map (function At x -> Some x | Key _ -> None) in
  match e.kind with
  | Int _ | Hex _ | Float _ | Bool _ | Str _ | Var _ | Keyword _ | Quote _ -> []
  | Vector es -> es
  | Record fs -> List.map snd fs
  | Get { record = x; _ } | Await x | Task_of x | Run x | Send x -> [ x ]
  | Read { target; path } -> target :: steps path
  | Set { target; path; value = last } | Update { target; path; func = last } ->
      (target :: steps path) @ [ last ]
  | Change { target; value } -> [ target; value ]
  | Fn l -> [ l.body ]
  | Let { bindings; body; _ } | Par_let { bindings; body } ->
      List.map snd bindings @ [ body ]
  | If { condition; then_branch; else_branch } -> [ condition; then_branch; else_branch ]
  | Match { scrutinee; clauses } -> scrutinee :: List.map snd clauses
  | Call { func; args } -> func :: args
  | Quasi q ->
      let rec holes = function
        | Unquote x -> [ x ]
        | Coll (_, items) ->
            List.concat_map (function Item q -> holes q | Splice x -> [ x ]) items
        | Leaf _ | Gensym _ -> []
      in
      holes q

(* What [e] does before it waits: the messages it sends, by their
   constructors, and the ! functions it calls. What a function value does,
   an @'s rest included, comes later. *)
let rec before_waiting e =
  let own =
    match e.kind with
    | Send { kind = Var c | Call { func = { kind = Var c; _ }; _ }; _ } -> [ `Sends c ]
    | Call { func = { kind = Var f; _ }; _ } when String.ends_with ~suffix:"!" f ->
        [ `Calls f ]
    | _ -> []
  in
  match e.kind with Fn _ -> [] | _ -> own @ List.concat_map before_waiting (children e)

(* The pattern of a handler, as Analyze builds it. *)
let handler_pattern e =
  match e.kind with
  | Fn { body = { kind = Match { clauses = (p, _) :: _; _ }; _ }; _ } -> Some p
  | _ -> None

(* The body a handler runs, after Lift. *)
let handler_body e =
  match e.kind with
  | Fn { body = { kind = Match { clauses = (_, some) :: _; _ }; _ }; _ } -> (
      match some.kind with
      | Call { args = [ { kind = Fn l; _ } ]; _ } -> Some l.body
      | _ -> None)
  | _ -> None

(* The file's names [e] changes with set! or update!. *)
let rec changes e =
  (match e.kind with Change { target = { kind = Var n; _ }; _ } -> [ n ] | _ -> [])
  @ List.concat_map changes (children e)

let is_type n = String.contains n '/' || (n <> "" && n.[0] >= 'A' && n.[0] <= 'Z')

(* The types a type as written names. *)
let rec type_names (node : Reader.node) =
  match node.form with
  | Symbol n when is_type n -> [ n ]
  | List items | Vector items -> List.concat_map type_names items
  | Map entries -> List.concat_map (fun (_, v) -> type_names v) entries
  | _ -> []

(* The global names an expression uses: names not bound inside it. *)
let references e =
  let found = Hashtbl.create 16 in
  let note n = Hashtbl.replace found n () in
  (* So are the types written on its names: code checked against a type
     is checked again when the type changes, as when a name does. *)
  let written w = Option.iter (fun w -> List.iter note (type_names w)) w in
  (* A constructor in a pattern is a reference too: a type that gains one
     breaks the match. *)
  let rec pat_names p =
    written p.written;
    match p.pat with
    | PVar n -> [ n ]
    | PCtor (c, ps) ->
        note c;
        List.concat_map pat_names ps
    | PVector ps -> List.concat_map pat_names ps
    | _ -> []
  in
  let rec go bound e =
    let go' = go bound in
    match e.kind with
    | Var n -> if not (List.mem n bound) then note n
    | Int _ | Hex _ | Float _ | Bool _ | Str _ | Keyword _ -> ()
    | Vector es -> List.iter go' es
    | Record fs -> List.iter (fun (_, v) -> go' v) fs
    | Get { record; _ } | Await record | Task_of record | Run record | Send record ->
        go' record
    | Read { target; path } ->
        go' target;
        List.iter (function At e -> go' e | Key _ -> ()) path
    | Set { target; path; value = last } | Update { target; path; func = last } ->
        go' target;
        List.iter (function At e -> go' e | Key _ -> ()) path;
        go' last
    | Change { target; value } ->
        go' target;
        go' value
    | Fn l ->
        List.iter (fun (b : binding) -> written b.written) l.params;
        go (List.map (fun b -> b.name) l.params @ bound) l.body
    | Let { bindings; body; how = Recursive } ->
        let bound = List.map (fun (b, _) -> b.name) bindings @ bound in
        List.iter
          (fun ((b : binding), v) ->
            written b.written;
            go bound v)
          bindings;
        go bound body
    | Let { bindings; body; _ } | Par_let { bindings; body } ->
        let bound =
          List.fold_left
            (fun bound ((b : binding), v) ->
              written b.written;
              go bound v;
              b.name :: bound)
            bound bindings
        in
        go bound body
    | If { condition; then_branch; else_branch } ->
        go' condition;
        go' then_branch;
        go' else_branch
    | Match { scrutinee; clauses } ->
        go' scrutinee;
        List.iter (fun (p, body) -> go (pat_names p @ bound) body) clauses
    | Call { func; args } ->
        go' func;
        List.iter go' args
    | Quote _ -> ()
    | Quasi q ->
        let rec quasi = function
          | Unquote e -> go' e
          | Coll (_, items) ->
              List.iter (function Item q -> quasi q | Splice e -> go' e) items
          | Leaf _ | Gensym _ -> ()
        in
        quasi q
  in
  go [] e;
  Hashtbl.fold (fun n () acc -> n :: acc) found [] |> List.sort compare

(* A type as written, with the names of its types mapped by [f]. *)
let rec rename_type f (node : Reader.node) =
  match node.form with
  | Symbol n when is_type n -> { node with form = Symbol (f n) }
  | List items -> { node with form = List (List.map (rename_type f) items) }
  | Vector items -> { node with form = Vector (List.map (rename_type f) items) }
  | Map entries ->
      { node with form = Map (List.map (fun (k, v) -> (k, rename_type f v)) entries) }
  | _ -> node

(* [e] with every global name (free variables, constructors) mapped by [f];
   names bound inside [e], or in [bound], are left alone. A call to a global is
   then given to [call], renamed, to rewrite. *)
let rename f ?(call = Fun.id) ?(bound = []) e =
  let written = Option.map (rename_type f) in
  let rec pat p =
    let p = if p.written = None then p else { p with written = written p.written } in
    match p.pat with
    | PCtor (c, ps) -> { p with pat = PCtor (f c, List.map pat ps) }
    | PVector ps -> { p with pat = PVector (List.map pat ps) }
    | _ -> p
  in
  let binding (b : binding) =
    if b.written = None then b else { b with written = written b.written }
  in
  let rec pat_names p =
    match p.pat with
    | PVar n -> [ n ]
    | PCtor (_, ps) | PVector ps -> List.concat_map pat_names ps
    | _ -> []
  in
  let rec go bound e =
    let go' = go bound in
    let steps = List.map (function At e -> At (go' e) | key -> key) in
    let kind =
      match e.kind with
      | Var n -> if List.mem n bound then e.kind else Var (f n)
      | (Int _ | Hex _ | Float _ | Bool _ | Str _ | Keyword _ | Quote _) as k -> k
      | Vector es -> Vector (List.map go' es)
      | Record fs -> Record (List.map (fun (k, v) -> (k, go' v)) fs)
      | Get g -> Get { g with record = go' g.record }
      | Read r -> Read { target = go' r.target; path = steps r.path }
      | Await x -> Await (go' x)
      | Task_of x -> Task_of (go' x)
      | Run x -> Run (go' x)
      | Set s -> Set { target = go' s.target; path = steps s.path; value = go' s.value }
      | Update u ->
          Update { target = go' u.target; path = steps u.path; func = go' u.func }
      | Change c -> Change { target = go' c.target; value = go' c.value }
      | Send x -> Send (go' x)
      | Fn l ->
          let body = go (List.map (fun b -> b.name) l.params @ bound) l.body in
          Fn { params = List.map binding l.params; body }
      | Let l ->
          let bindings, body = let_ ~self:(l.how = Recursive) bound l.bindings l.body in
          Let { l with bindings; body }
      | Par_let { bindings; body } ->
          let bindings, body = let_ bound bindings body in
          Par_let { bindings; body }
      | If { condition; then_branch; else_branch } ->
          If
            {
              condition = go' condition;
              then_branch = go' then_branch;
              else_branch = go' else_branch;
            }
      | Match { scrutinee; clauses } ->
          Match
            {
              scrutinee = go' scrutinee;
              clauses =
                List.map (fun (p, body) -> (pat p, go (pat_names p @ bound) body)) clauses;
            }
      | Call { func; args } -> (
          match func.kind with
          (* A ! added to a call of a local function. *)
          | Var n
            when String.ends_with ~suffix:"!" n
                 && (not (List.mem n bound))
                 && List.mem (unbang n) bound ->
              let func = { func with kind = Var (unbang n); origin = Some "!" } in
              Call { func; args = List.map go' args }
          | Var n when not (List.mem n bound) ->
              (call { e with kind = Call { func = go' func; args = List.map go' args } })
                .kind
          | _ -> Call { func = go' func; args = List.map go' args })
      | Quasi q ->
          let rec quasi = function
            | Unquote x -> Unquote (go' x)
            | Coll (c, items) ->
                Coll
                  ( c,
                    List.map
                      (function Item q -> Item (quasi q) | Splice x -> Splice (go' x))
                      items )
            | q -> q
          in
          Quasi (quasi q)
    in
    { e with kind }
  and let_ ?(self = false) bound bindings body =
    let bound, bindings =
      List.fold_left
        (fun (bound, acc) (b, v) ->
          let v = go (if self then b.name :: bound else bound) v in
          (b.name :: bound, (binding b, v) :: acc))
        (bound, []) bindings
    in
    (List.rev bindings, go bound body)
  in
  go bound e
