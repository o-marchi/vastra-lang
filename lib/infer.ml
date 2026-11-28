(* Hindley–Milner inference with levels (Rémy), rows (Leijen, "Extensible
   records with scoped labels") and constrained variables (number, comparable,
   equatable, as in Elm, and integer). The order of operations decides which
   error is reported first and the order of keys in displayed rows: keep it
   stable. *)

open Types
module Env = Map.Make (String)
module Ints = Map.Make (Int)

(* Constructor fields use [Gen i] for the type's parameters. [shape]: the map
   type a type names instead. *)
type typedef = {
  params : int;
  ctors : (string * Types.t list) list;
  equatable : bool;
  shape : Types.t option;
  words : (string * string) list; (* each constructor's outside word *)
}

(* The module being defined, and the names it brought in with :require. *)
type scope = {
  module_ : string option;
  aliases : (string * string) list;
  refers : (string * string) list;
}

(* A name's unknown: open, or fixed to a type by a use, which an error
   over a disagreement names ("by `add`", "at app.vas:3"). *)
type unknown = Open of constr option | Fixed of Types.t * string

type env = {
  vars : scheme Env.t;
  types : typedef Env.t; (* by key: see [type_key] *)
  ctors : string Env.t; (* constructor → its type's key *)
  suspended : string Env.t; (* definition → the redefinition that suspended it *)
  scope : scope;
  type_versions : int Env.t; (* types whose definition changed *)
  unknowns : unknown Ints.t;
  changing : string Env.t; (* the names the files' code set!s, and where *)
  messages : Types.t option; (* the messages the page's handlers and views share *)
}

(* Where a type's current definition is: its name, then a number for each
   version. Values of an older version keep it, and never meet the new one. *)
let type_key env name =
  match Env.find_opt name env.type_versions with
  | Some v -> name ^ " " ^ string_of_int v
  | None -> name

(* A named map stands for its map, as if written where it is used, so the
   types in it are their current versions. *)
let rec current env = function
  | Con (key, args) ->
      let name = List.hd (String.split_on_char ' ' key) in
      Con (type_key env name, List.map (current env) args)
  | Fun (ps, r, a) -> Fun (List.map (current env) ps, current env r, current env a)
  | Record row -> Record (current env row)
  | Row_extend (k, t, rest) -> Row_extend (k, current env t, current env rest)
  | t -> t

(* A name as you would type it here, the reverse of Session.resolve:
   plain where a plain name reaches it, else through an alias, else qualified. *)
let shown env name =
  let name = List.hd (String.split_on_char ' ' name) in
  match String.rindex_opt name '/' with
  | None -> name
  | Some i -> (
      let m = String.sub name 0 i in
      let x = String.sub name (i + 1) (String.length name - i - 1) in
      let own = env.scope.module_ in
      let mine x =
        Option.fold own ~none:false ~some:(fun o ->
            let q = o ^ "/" ^ x in
            Env.mem q env.vars || Env.mem q env.types || Env.mem q env.ctors)
      in
      if own = Some m || (List.assoc_opt x env.scope.refers = Some name && not (mine x))
      then x
      else
        match List.find_opt (fun (_, q) -> q = m) env.scope.aliases with
        | Some (a, _) -> a ^ "/" ^ x
        | None -> name)

let primitive n = { params = n; ctors = []; equatable = true; shape = None; words = [] }

let empty_env =
  {
    vars = Env.empty;
    types =
      Env.of_list
        (List.map (fun t -> (Num.name t, primitive 0)) Num.all
        @ [
          ("String", primitive 0);
          ("Bool", primitive 0);
          ("Unit", primitive 0);
          ("Vector", primitive 1);
          ("Buffer", primitive 1);
          (* A vector's kind (Types.vector): a buffer is not equatable. *)
          ("shared", primitive 0);
          ("unique", { (primitive 0) with equatable = false });
          ("Dict", primitive 2);
          ("Form", { (primitive 0) with equatable = false });
          ("Task", { (primitive 2) with equatable = false });
          ("Running", { (primitive 0) with equatable = false });
        ]);
    ctors = Env.empty;
    suspended = Env.empty;
    scope = { module_ = None; aliases = []; refers = [] };
    type_versions = Env.empty;
    unknowns = Ints.empty;
    changing = Env.empty;
    messages = None;
  }

type var_state =
  | Unbound of int * constr option
  (* level, constraint *)
  | Link of Types.t

type unify_error =
  | Mismatch of Types.t * Types.t
  | Arity of { expected : int; found : int }
  | Occurs of int * Types.t
  | Missing_key of { key : string; available : string list }
  | Extra_key of string * string option (* and the key meant, if one was *)
  | Recursive_row
  | Key of string * Types.t * Types.t * unify_error (* at this key of two maps *)
  | Inside of unify_error (* inside a vector, a constructor or a function *)
  | Outside of held * Num.fixed (* a literal this type does not hold *)
  | Held of string (* a buffer where none can be, and why *)

(* A literal a number variable must hold, and the generic function it
   comes from, if it isn't written here. *)
and held = Z.t * string option

exception Unify of unify_error

(* Where code is, for what may change the file's names: the top level
   (the file, a handler, the prompt), a macro, or a function, named or not,
   at a point that runs when its task runs (after an @) or when it is called. *)
type place =
  | Top
  | Macro_body
  | View_body
  | In_fn of { name : string option; waiting : bool }

type site =
  | Argument of { index : int; func : string option; origin : string option }
  | Callee of string option
  | Condition of string option (* the macro that wrote the if *)
  | Branches of string option
  | Key_access of string
  | Changed_key of string
  | Path_step
  | Path_key
  | Kept_element
  | Kept_type of string * string (* a name a change keeps, and the forms *)
  | Awaited
  | Returned of { index : int; func : string option; origin : string option }
    (* the body of a function passed as an argument *)
  | Element
  | Pattern
  | Clauses of string option (* the macro that wrote the match *)
  | Failure_clause (* of a let *)
  | Recursion of string
  | Unquoted
  | Message (* the file's messages *)
  | View_html
  | View_pixels
  | Written of string (* a name and the type written for it *)
  | Untold of string (* a native no written type told *)

(* A call that may change the file's names, as written: whether it
   shows a !, in the name it calls or [added] to the call. *)
type call = {
  action : Types.t; (* whether it acts *)
  at : Reader.span;
  shows : bool;
  added : bool;
  passes : bool; (* it is given a parameter, and acts when that does *)
  callee : string option;
  given : (Ast.expr * Types.t) list; (* its arguments, and what it takes for each *)
}

type checker = {
  env : env;
  mutable locals : (string * scheme) list;
  table : var_state Dynarray.t;
  mutable level : int;
  mutable self : scheme option; (* a function's own name, inside its body *)
  mutable generic : int list; (* the number variables generic functions are told *)
  mutable later : (unit -> unit) list; (* notes for running code, once types are known *)
  holds : (int, held * held) Hashtbl.t; (* the lowest and highest a number variable must hold *)
  mutable unknowns : unknown Ints.t; (* the names' unknowns, as this check leaves them *)
  stand_ins : (int, Types.t) Hashtbl.t; (* an unknown's variable in this check *)
  named : (int, int * string) Hashtbl.t; (* and back: a variable's unknown *)
  opened : int option; (* a fixed unknown taken as open, to see if an error is over it *)
  mutable outside : (string * scheme) list; (* the locals from outside the function *)
  mutable around : (string * scheme) list;
      (* the same, for the function as written: the functions @ makes are not *)
  mutable making : string list; (* the names functions made in a let's value use *)
  mutable made : (scheme * string list) list; (* and those of each let, by its scheme *)
  mutable place : place;
  mutable naming : string option; (* the name of the function inferred next *)
  mutable acts : Types.t; (* whether the function being inferred acts *)
  mutable calls : call list; (* its calls that may act, newest first *)
  mutable params : (string * scheme) list; (* the parameters of the functions around *)
  mutable plain : string option; (* the plain function the code is in, if any *)
  mutable messages : Types.t option; (* the file's messages, as far as known *)
  mutable origin : string option; (* the macro that made that function *)
  line : int -> int; (* the line of a byte of the source, for Once *)
  (* For Once: each local's type, what each get gives, what each vector holds. *)
  mutable bound : (Ast.binding * Types.t) list;
  mutable matched : (Ast.pattern * Types.t) list;
  mutable got : (Ast.expr * Types.t) list;
  (* The natives waiting to be told a written type, with what they give
     otherwise. *)
  mutable telling : (Types.t * Types.t * Ast.expr) list;
  (* Where each variable was fixed, in this check: an error underlines it too,
     and the place being checked. *)
  fixed : (int, Reader.span) Hashtbl.t;
  mutable checking : Reader.span;
}

let checker env =
  {
    env;
    locals = [];
    table = Dynarray.create ();
    level = 1;
    self = None;
    generic = [];
    later = [];
    holds = Hashtbl.create 8;
    unknowns = env.unknowns;
    stand_ins = Hashtbl.create 4;
    named = Hashtbl.create 4;
    opened = None;
    outside = [];
    around = [];
    making = [];
    made = [];
    place = Top;
    naming = None;
    acts = Types.plain;
    calls = [];
    params = [];
    plain = None;
    messages = env.messages;
    origin = None;
    line = (fun _ -> 0);
    bound = [];
    matched = [];
    got = [];
    telling = [];
    fixed = Hashtbl.create 8;
    checking = Diagnostic.nowhere;
  }

let later c note = c.later <- note :: c.later

let fresh_at ?constr c level =
  Dynarray.add_last c.table (Unbound (level, constr));
  Var (Dynarray.length c.table - 1)

let fresh ?constr c = fresh_at ?constr c c.level

let state c v =
  match Dynarray.get c.table v with Unbound (l, k) -> (l, k) | Link _ -> (c.level, None)

let level_of c v = fst (state c v)

let rec resolve c = function
  | Var v as ty -> (
      match Dynarray.get c.table v with Link t -> resolve c t | Unbound _ -> ty)
  | ty -> ty

(* An unknown left open shows as itself. [lazily]: so does one this check
   fixed, as the session keeps it. *)
let rec zonk ?(lazily = false) c ty =
  match ty with
  | Var v -> (
      match (Dynarray.get c.table v, Hashtbl.find_opt c.named v) with
      | Link _, Some (u, owner) when lazily -> Unknown (u, owner)
      | Link t, _ -> zonk ~lazily c t
      | Unbound _, Some (u, owner) -> Unknown (u, owner)
      | Unbound _, None -> ty)
  | Con (n, args) -> Con (n, List.map (zonk ~lazily c) args)
  | Fun (ps, r, e) ->
      Fun (List.map (zonk ~lazily c) ps, zonk ~lazily c r, zonk ~lazily c e)
  | Record row -> Record (zonk ~lazily c row)
  | Row_extend (k, f, rest) -> Row_extend (k, zonk ~lazily c f, zonk ~lazily c rest)
  | ty -> ty

(* Types as errors show them. *)
let namer_of c =
  namer ~plain:true
    ~constr_of:(function
      | Var v -> (
          match snd (state c v) with Some (Child h) -> Some (Child (zonk c h)) | k -> k)
      | _ -> None)
    ~shown:(shown c.env) ()

let rec map_type f = function
  | Con (n, args) -> Con (n, Util.map_in_order (map_type f) args)
  | Fun (ps, r, e) ->
      let ps = Util.map_in_order (map_type f) ps in
      let r = map_type f r in
      Fun (ps, r, map_type f e)
  | Record row -> Record (map_type f row)
  | Row_extend (k, fld, rest) ->
      let fld = map_type f fld in
      Row_extend (k, fld, map_type f rest)
  | ty -> f ty

(* [f] on the types in a constraint: a child's html. *)
let rec map_constr f = function
  | Child h -> Child (f h)
  | Optional k -> Optional (Option.map (map_constr f) k)
  | k -> k

(* Quantify the variables deeper than the current level, and those in their
   constraints. *)
let generalize c ty =
  let gens = ref [] in
  let rec gen = function
    | Var v when level_of c v > c.level -> (
        match List.assoc_opt v !gens with
        | Some (g, _) -> Gen g
        | None ->
            let g = List.length !gens in
            gens := (v, (g, None)) :: !gens;
            let k = Option.map (map_constr (fun h -> map_type gen (zonk c h))) in
            gens := (v, (g, k (snd (state c v)))) :: List.remove_assoc v !gens;
            Gen g)
    | ty -> ty
  in
  let ty = map_type gen (zonk c ty) in
  let vars = Array.make (List.length !gens) None in
  List.iter (fun (_, (g, k)) -> vars.(g) <- k) !gens;
  let holds =
    List.filter_map
      (fun (v, (g, _)) ->
        Option.map (fun ((lo, _), (hi, _)) -> (g, (lo, hi))) (Hashtbl.find_opt c.holds v))
      !gens
  in
  { vars; ty; holds; reads = []; told = None }

(* The variables of [ty] that [generalize] quantifies and a generic function
   is told, in the order of its scheme. *)
let told_vars c ty =
  let found = ref [] in
  ignore
    (map_type
       (function
         | Var v as t ->
             let level, k = state c v in
             if level > c.level && told k && not (List.mem v !found) then
               found := v :: !found;
             t
         | t -> t)
       (zonk c ty));
  List.rev !found

let substitute fresh ty = map_type (function Gen i -> fresh.(i) | t -> t) ty

(* A name the code changes holds one type. A map written out in it may
   be seen with keys that may be missing, which it leaves out: where the
   name changes, it gains none. *)
let one_type (s : scheme) =
  Array.for_all (function Some (Optional _) -> true | _ -> false) s.vars

let close c ty =
  let optional v = match snd (state c v) with Some (Optional _) -> true | _ -> false in
  ignore
    (map_type
       (function
         | Var v when optional v ->
             Dynarray.set c.table v (Link Row_empty);
             Row_empty
         | t -> t)
       (zonk c ty));
  ty

(* The variable for a name's unknown in this check, at level 0 so that it is
   never generalized; bound to its type if a use fixed it. *)
let rec stand_in c u owner =
  match Hashtbl.find_opt c.stand_ins u with
  | Some t -> t
  | None ->
      let v = Dynarray.length c.table in
      let constr, fixed =
        match Ints.find u c.unknowns with
        | Open k -> (k, None)
        | Fixed (t, _) when c.opened <> Some u -> (None, Some t)
        | Fixed _ -> (None, None)
      in
      Dynarray.add_last c.table (Unbound (0, constr));
      Hashtbl.replace c.stand_ins u (Var v);
      Hashtbl.replace c.named v (u, owner);
      Option.iter (fun t -> Dynarray.set c.table v (Link (knowns c t))) fixed;
      Var v

and knowns c ty = map_type (function Unknown (u, owner) -> stand_in c u owner | t -> t) ty

(* [ty] must hold the literals from [low] to [high]. *)
let hold c ty (((lo, _) as low), ((hi, _) as high)) =
  match resolve c ty with
  | Var u ->
      let r =
        match Hashtbl.find_opt c.holds u with
        | Some ((((a, _) as l), ((b, _) as h))) ->
            ((if Z.lt lo a then low else l), if Z.gt hi b then high else h)
        | None -> (low, high)
      in
      Hashtbl.replace c.holds u r
  | Con (name, []) when Num.is_name name -> (
      match Num.of_name name with
      | Fixed f ->
          let min, max = Num.range f in
          if Z.lt lo min then raise (Unify (Outside (low, f)));
          if Z.gt hi max then raise (Unify (Outside (high, f)))
      | Int | Float -> ())
  | _ -> ()

let literal c ty n = hold c ty ((n, None), (n, None))

(* Fresh variables for [s]'s, holding what the literals of [from] need. *)
let fresh_vars ?from c (s : scheme) =
  let fresh = Array.map (fun constr -> fresh ?constr c) s.vars in
  (* A constraint's types are in the scheme's variables. *)
  Array.iter2
    (fun v k ->
      match (v, k) with
      | Var v, Some k ->
          let k = map_constr (substitute fresh) k in
          Dynarray.set c.table v (Unbound (c.level, Some k))
      | _ -> ())
    fresh s.vars;
  List.iter (fun (g, (lo, hi)) -> hold c fresh.(g) ((lo, from), (hi, from))) s.holds;
  fresh

let instantiate c (s : scheme) = knowns c (substitute (fresh_vars c s) s.ty)

(* A number type as running code finds it: known here, or told to a generic
   function around it. One that nothing fixed is an Int. *)
let num c ty : Ast.num =
  match resolve c ty with
  | Con (name, []) -> Known (Num.of_name name)
  | Var v when List.mem v c.generic -> Hidden v
  | _ -> Known Int

(* Only functions are generic over number. One is told the types of
   these variables. *)
let generic c (fn : Ast.expr) ty =
  let vars = told_vars c ty in
  c.generic <- vars @ c.generic;
  if vars <> [] then fn.typed <- Generic vars

(* Any other value keeps one number type, which what uses it fixes... *)
let monomorphic c ty =
  List.iter
    (fun v -> Dynarray.set c.table v (Unbound (c.level, snd (state c v))))
    (told_vars c ty)

(* Does [v] occur in [ty]? Also lowers [ty]'s variables to [level]. *)
let rec occurs c v level ty =
  match resolve c ty with
  | Var u when u = v -> true
  | Var u ->
      let l, k = state c u in
      if l > level then (
        Dynarray.set c.table u (Unbound (level, k));
        (* A child's html goes with it. *)
        match k with Some (Child h) -> ignore (occurs c v level h) | _ -> ());
      false
  | Con (_, args) -> List.exists (occurs c v level) args
  | Fun (ps, r, e) -> List.exists (occurs c v level) (e :: r :: ps)
  | Record row -> occurs c v level row
  | Row_extend (_, f, rest) -> occurs c v level f || occurs c v level rest
  | _ -> false

(* :k? for :k, and :k for :k?: keys that are one outside. *)
let twin key =
  if Util.may_miss key then String.sub key 0 (String.length key - 1) else key ^ "?"

exception Unsatisfied

(* Make [ty] meet constraint [k], constraining its variables where needed. *)
let rec satisfy c k ty =
  match resolve c ty with
  | Var u -> (
      let l, k' = state c u in
      let set k = Dynarray.set c.table u (Unbound (l, Some k)) in
      match (k, k') with
      (* A child holds no buffer, is no number, and only a String compares
         (an element holds functions). *)
      | Child h, Some (Child h') -> unify c h h'
      | Child h, (None | Some (Bufferless _)) ->
          set k;
          ignore (occurs c u l h)
      | Bufferless _, Some (Child _) -> ()
      | Child _, Some (Comparable | Equatable)
      | (Comparable | Equatable), Some (Child _) ->
          Dynarray.set c.table u (Link str)
      | Child _, Some _ | _, Some (Child _) -> raise Unsatisfied
      | _ -> set (match k' with Some k' -> stronger k k' | None -> k))
  | ty when (match k with Child _ -> true | _ -> false) -> child c k ty
  | ty when (match k with Bufferless _ -> true | _ -> false) -> bufferless c k ty
  | ty when (match k with Optional _ -> true | _ -> false) -> optional c k ty
  (* Every number type is comparable; all but Float are integers. *)
  | Con (name, []) when Num.is_name name && not (k = Integer && name = "Float") -> ()
  | Con ("String", []) when k = Comparable || k = Equatable -> ()
  (* A buffer is not equatable: a vector or a buffer compared is a vector. *)
  | Con ("Vector", [ a; m ]) when k = Equatable ->
      (match resolve c m with
      | Var u -> Dynarray.set c.table u (Link shared)
      | m -> satisfy c k m);
      satisfy c k a
  | Con (name, args) when k = Equatable && (Env.find name c.env.types).equatable ->
      List.iter (satisfy c Equatable) args
  | Record r when k = Equatable -> satisfy c k r
  | Row_extend (_, f, rest) when k = Equatable ->
      satisfy c k f;
      satisfy c k rest
  | Row_empty when k = Equatable -> ()
  | _ -> raise Unsatisfied

(* [ty] holds no buffer: each vector or buffer in it a vector, and each
   variable constrained by [k], which says why. Vectors, dictionaries and
   tasks hold none, and functions none from outside. *)
and bufferless c k ty =
  match resolve c ty with
  | Var _ as v -> satisfy c k v
  | Con ("Vector", [ a; m ]) ->
      (match (resolve c m, k) with
      | Var u, _ -> Dynarray.set c.table u (Link shared)
      | m, Bufferless why when m = unique -> raise (Unify (Held why))
      | _ -> ());
      bufferless c k a
  | Con (("Dict" | "Task"), _) | Fun _ -> ()
  | Con (_, ts) -> List.iter (bufferless c k) ts
  | Record r -> bufferless c k r
  | Row_extend (_, t, r) ->
      bufferless c k t;
      bufferless c k r
  | _ -> ()

(* [ty] a row of keys that may be missing, each meeting the constraint
   [k] has for them. *)
and optional c k ty =
  match (resolve c ty, k) with
  | Row_extend (key, f, rest), Optional keys ->
      if not (Util.may_miss key) then raise (Unify (Extra_key (key, None)));
      Option.iter (fun k -> satisfy c k f) keys;
      optional c k rest
  | (Var _ as v), _ -> satisfy c k v
  | _ -> ()

(* A child of html: an element of that html, a String, or a vector of
   children. *)
and child c k ty =
  match (resolve c ty, k) with
  | Con ("String", []), _ -> ()
  | Con ("Vector", [ a; m ]), _ ->
      (match resolve c m with
      | Var u -> Dynarray.set c.table u (Link shared)
      | m -> if m = unique then raise Unsatisfied);
      satisfy c k a
  | (Con (n, _) as element), Child (Con (h, _) as html) when n = h -> unify c html element
  | _ -> raise Unsatisfied

(* [mismatch]: the error if [ty] does not meet [v]'s constraint. *)
and bind c v ty mismatch =
  let level, constr = state c v in
  if occurs c v level ty then raise (Unify (Occurs (v, ty)));
  (match constr with
  | Some k -> ( try satisfy c k ty with Unsatisfied -> raise (Unify mismatch))
  | None -> ());
  Option.iter (hold c ty) (Hashtbl.find_opt c.holds v);
  if c.checking.start >= 0 then Hashtbl.replace c.fixed v c.checking;
  Dynarray.set c.table v (Link ty)

and row_tail c row =
  match resolve c row with
  | Row_extend (_, _, rest) -> row_tail c rest
  | Var v -> Some v
  | _ -> None

(* Bring [key] to the front of [row]: its type and the rest. A row variable is
   extended with the key; [seen] collects passed keys for "did you mean". *)
and rewrite_row c row key seen =
  match resolve c row with
  | Row_extend (k, f, rest) when k = key -> (f, rest)
  | Row_extend (k, f, rest) ->
      let found, rest = rewrite_row c rest key (k :: seen) in
      (found, Row_extend (k, f, rest))
  | Var v ->
      let missing = Unify (Missing_key { key; available = List.rev seen }) in
      (* A map with :k and :k? has one of them by mistake. *)
      if List.mem (twin key) seen then raise (Unify (Extra_key (twin key, Some key)));
      (* The new field and tail inherit the row variable's constraint. A map
         written out has all its keys but those that may be missing. *)
      let level, constr = state c v in
      let keys =
        match constr with
        | Some (Optional _) when not (Util.may_miss key) -> raise missing
        | Some (Optional keys) -> keys
        | k -> k
      in
      let f = fresh_at ?constr:keys c level and rest = fresh_at ?constr c level in
      Dynarray.set c.table v (Link (Row_extend (key, f, rest)));
      (f, rest)
  | Row_empty -> raise (Unify (Missing_key { key; available = List.rev seen }))
  | other -> raise (Unify (Mismatch (Row_empty, other)))

and unify c a b =
  let a = resolve c a and b = resolve c b in
  match (a, b) with
  | Var x, Var y when x = y -> ()
  (* The deeper variable goes, so that a name's unknown stays itself. *)
  | Var x, Var y when level_of c x < level_of c y -> bind c y a (Mismatch (a, b))
  | Var v, other -> bind c v other (Mismatch (a, b))
  | other, Var v -> (
      (* A map written out, found where it needs more keys, misses them. *)
      try bind c v other (Mismatch (a, b))
      with Unify (Extra_key (key, _)) -> raise (Unify (Missing_key { key; available = [] })))
  | Row_empty, Row_empty -> ()
  (* A buffer and a vector differ as wholes. *)
  | Con ("Vector", [ x; m ]), Con ("Vector", [ y; n ]) ->
      (try unify c m n with Unify _ -> raise (Unify (Mismatch (a, b))));
      inside (fun () -> unify c x y)
  | Con (n, xs), Con (m, ys) when n = m && List.length xs = List.length ys ->
      inside (fun () -> List.iter2 (unify c) xs ys)
  | Fun (pa, ra, ea), Fun (pb, rb, eb) ->
      if List.length pa <> List.length pb then
        raise (Unify (Arity { expected = List.length pa; found = List.length pb }));
      inside (fun () ->
          List.iter2 (unify c) pa pb;
          unify c ra rb);
      (* One that acts where a plain one is promised differs as a whole. *)
      (try unify c ea eb with Unify _ -> raise (Unify (Mismatch (a, b))))
  | Record ra, Record rb -> unify c ra rb
  | Row_extend (key, f, rest), _ ->
      let tail = row_tail c rest in
      let f', rest' = rewrite_row c b key [] in
      (* Leijen's side condition: binding our own tail would make the rows infinite. *)
      (match tail with
      | Some t
        when match Dynarray.get c.table t with Link _ -> true | Unbound _ -> false ->
          raise (Unify Recursive_row)
      | _ -> ());
      (try unify c f f' with Unify e -> raise (Unify (Key (key, f, f', e))));
      unify c rest rest'
  | Row_empty, Row_extend (key, _, _) -> raise (Unify (Extra_key (key, None)))
  | _ -> raise (Unify (Mismatch (a, b)))

(* A path of keys stops at a vector, a constructor or a function. *)
and inside f = try f () with Unify (Key _ as e) -> raise (Unify (Inside e))

(* A type shown [s] as a sentence says it: a map {:a Int}, an (Option Int),
   a U8 (said "you"). *)
let kind s = function
  | Record _ -> "a map " ^ s
  | Fun _ -> "a function " ^ s
  | _ ->
      let first = if s.[0] = '(' then 1 else 0 in
      (if String.contains "aeioAEIO" s.[first] then "an " else "a ") ^ s

(* A type as a sentence names it: a map, a function, a vector, a String. *)
let described n = function
  | Record _ -> "a map"
  | Fun _ -> "a function"
  | Con ("Vector", _) -> "a vector"
  | t ->
      let s = show_with n t in
      (if String.contains "AEIOU" s.[0] then "an " else "a ") ^ s

let explain c error expected found span site =
  let n = namer_of c in
  let expected_at =
    match expected with Var v -> Hashtbl.find_opt c.fixed v | _ -> None
  in
  let a t = (if (Num.name t).[0] = 'I' then "an " else "a ") ^ Num.name t in
  (* The keys down to the difference, and the two types there. *)
  let rec dig path there = function
    | Key (k, a, b, e) -> dig (k :: path) (a, b) e
    | e -> (List.rev path, there, e)
  in
  let path, (expected, found), error = dig [] (expected, found) error in
  let expected_s, found_s =
    match error with
    | Inside _ -> differ n (zonk c expected) (zonk c found)
    | _ ->
        let e = show_with n (zonk c expected) in
        (e, show_with n (zonk c found))
  in
  let mismatch = Printf.sprintf "expected %s, found %s" expected_s found_s in
  (* Two versions of a type print alike. *)
  let rec names acc = function
    | Con (n, args) -> List.fold_left names (n :: acc) args
    | Fun (ps, r, _) -> List.fold_left names acc (r :: ps)
    | Record r -> names acc r
    | Row_extend (_, t, rest) -> names (names acc t) rest
    | _ -> acc
  in
  let theirs = names [] (zonk c found) in
  let versions =
    List.find_opt
      (fun n -> List.exists (fun m -> m <> n && shown c.env m = shown c.env n) theirs)
      (names [] (zonk c expected))
  in
  (* The headline says what the type is for, in the form as written;
     [restated] when it says what the context note would. *)
  let want, got = (kind expected_s (zonk c expected), kind found_s (zonk c found)) in
  let headline, restated =
    match (versions, site) with
    | _ when path <> [] -> (mismatch, false)
    | Some v, _ ->
        let v = shown c.env v in
        (Printf.sprintf "this is a %s made before `%s` changed" v v, false)
    | _, Argument { func = Some g; origin = None; _ } when g <> "macro/later-dropping" ->
        (Printf.sprintf "`%s` takes %s, and this is %s" (shown c.env g) want got, false)
    | _, Condition (Some "cond") -> ("a cond's test is a Bool, and this is " ^ got, true)
    | _, (Condition (Some (("and" | "or") as m)) | Branches (Some (("and" | "or") as m)))
      ->
        (Printf.sprintf "`%s` takes Bools, and this is %s" m got, true)
    | _, Condition None -> ("an if's condition is a Bool, and this is " ^ got, true)
    | _, Branches None ->
        (Printf.sprintf "this branch gives %s, and the other %s" got want, true)
    | _, (Branches (Some "cond") | Clauses (None | Some "later")) ->
        (Printf.sprintf "this result is %s, and the one before %s" got want, true)
    | _, Element ->
        (Printf.sprintf "this element is %s, and the one before %s" got want, true)
    | _, Pattern ->
        ( Printf.sprintf "this pattern matches %s, and the value matched is %s" got want,
          true )
    | _ -> (mismatch, false)
  in
  let where = String.concat " " (List.map (( ^ ) ":") path) in
  let at message =
    Diagnostic.make Type span
      (if path = [] then message else "at " ^ where ^ ": " ^ message)
  and note = Diagnostic.note in
  let both d = d |> note ("expected: " ^ expected_s) |> note ("found:    " ^ found_s) in
  let rekey old key = Diagnostic.fix (Edit (span, Diagnostic.rekey old key)) in
  let child t =
    match resolve c t with
    | Var v -> ( match snd (state c v) with Some (Child _) -> true | _ -> false)
    | _ -> false
  in
  let constrained t =
    match resolve c t with
    | Var v -> (
        match snd (state c v) with
        | Some ((Comparable | Equatable) as k) -> Some k
        | _ -> None)
    | _ -> None
  in
  let d =
    match error with
    | Mismatch (a, b) when child a <> child b ->
        let other = zonk c (if child a then b else a) in
        let rule = "a child of html is an element, a String, or a list of them" in
        let d =
          if child expected <> child found then
            at (rule ^ "; this has type " ^ show_with n other)
          else at mismatch |> note (rule ^ ", not " ^ show_with n other)
        in
        if match other with Record _ -> true | _ -> false then
          note "an element's attributes are a map written in place, right after its tag" d
        else d
    | Mismatch (a, b) when constrained a <> None || constrained b <> None -> (
        (* What a constraint allows, in words. *)
        let k, other =
          if constrained a <> None then (constrained a, b) else (constrained b, a)
        in
        let other = zonk c other in
        let who name =
          match site with Argument { func = Some g; _ } -> shown c.env g | _ -> name
        in
        match (k, other) with
        | Some Comparable, _ ->
            at
              (Printf.sprintf "`%s` compares numbers and Strings, and %s is neither"
                 (who "<") (described n other))
        | _, Fun _ -> at (Printf.sprintf "`%s` can't compare functions" (who "="))
        | _ ->
            at
              (Printf.sprintf "`%s` can't compare %s, since it holds a function" (who "=")
                 (described n other)))
    | Mismatch (a, b) ->
        let a = show_with n (zonk c a) in
        let b = show_with n (zonk c b) in
        let d =
          if a <> expected_s || b <> found_s then
            at headline |> note (a ^ " does not match " ^ b)
          else at headline
        in
        (* Only an element's messages can differ from a child's html's. *)
        if child expected <> child found then
          note "an element's children share its type of message" d
        else d
    | Arity { expected; found } -> (
        match site with
        | Argument { func = Some g; origin = None; _ } when path = [] ->
            at
              (Printf.sprintf "`%s` calls this with %s, and it takes %d" (shown c.env g)
                 (Diagnostic.plural expected "argument")
                 found)
        | _ ->
            at mismatch
            |> note
                 (Printf.sprintf "a function of %s does not match a function of %s"
                    (Diagnostic.plural expected "argument")
                    (Diagnostic.plural found "argument")))
    | Occurs _ -> at "this would need a type that contains itself"
    | Missing_key { key; available } -> (
        let headline =
          match site with
          | Argument { func = Some g; origin = None; _ } when path = [] ->
              let g = shown c.env g in
              Printf.sprintf "`%s` reads :%s, and this map has no :%s" g key key
          | _ -> "missing key :" ^ key
        in
        let d = both (at headline) in
        (* The typo is in what is underlined: a path's key, or else the map. *)
        match (Diagnostic.suggest key available, site) with
        | Some s, Changed_key _ -> Diagnostic.fix (Edit (span, fun _ -> Some (":" ^ s))) d
        | Some s, _ -> rekey s key d
        | None, _ -> d)
    | Extra_key (key, s) ->
        let d = both (at ("unexpected key :" ^ key)) in
        Option.fold s ~none:d ~some:(fun s -> rekey key s d)
    | Recursive_row -> at mismatch |> note "these maps would need infinitely many keys"
    | Outside ((n, from), f) ->
        let lo, hi = Num.range f in
        let n = Z.to_string n in
        at
          (match from with
          | None -> Printf.sprintf "%s doesn't fit in %s" n (a (Fixed f))
          | Some g -> Printf.sprintf "`%s` needs a number type that holds %s" (shown c.env g) n)
        |> note (Printf.sprintf "%s holds %s to %s" (a (Fixed f)) (Z.to_string lo) (Z.to_string hi))
    | Inside _ | Key _ -> at headline
    | Held why -> at why
  in
  (* Two number types never mix: the conversions that would join them. Nothing
     converts a Float to a whole number. *)
  let rec innermost = function Inside e | Key (_, _, _, e) -> innermost e | e -> e in
  let d =
    match innermost error with
    | Mismatch (x, y) -> (
        match (zonk c x, zonk c y) with
        | Con (x, []), Con (y, []) when Num.is_name x && Num.is_name y && x <> y ->
            let x = Num.of_name x and y = Num.of_name y in
            let into t from =
              if from = Num.Float then [] else [ "to-" ^ String.lowercase_ascii (Num.name t) ]
            in
            note
              (Printf.sprintf "%s and %s don't mix: convert with %s" (a x) (a y)
                 (String.concat " or " (into x y @ into y x)))
              d
        | _ -> d)
    | _ -> d
  in
  let d =
    if versions = None then d
    else note "a value keeps the version of its type it was made with" d
  in
  let f = shown c.env in
  let context =
    match site with
    | Argument { origin = Some "@"; _ } | Returned { origin = Some "@"; _ } ->
        "tasks awaited together with @ must fail with the same error type: task/map-err \
         converts one"
    | Returned { origin = Some "later"; _ } ->
        "the clauses of later run on their own, so they cannot fail: handle each failure \
         in them"
    | Argument { func = Some "macro/later-dropping"; _ } ->
        "later runs it on its own, so its clauses take each end: \
         (later (http/get-text url) [(Ok text) ...] [(Err why) ...])"
    | Argument { origin = Some m; _ } -> Printf.sprintf "in this use of `%s`" (f m)
    | Argument { index; func = Some g; _ } ->
        Printf.sprintf "in argument %d of `%s`" (index + 1) (f g)
    | Argument { index; _ } -> Printf.sprintf "in argument %d" (index + 1)
    | Callee (Some g) -> Printf.sprintf "`%s` is called as a function here" (f g)
    | Callee None -> "this is called as a function here"
    (* As written: cond, and, or and later are ifs and matches. *)
    | Condition (Some "cond") -> "each test of a cond must be a Bool"
    | (Condition (Some (("and" | "or") as m)) | Branches (Some (("and" | "or") as m))) ->
        Printf.sprintf "`%s` takes Bools" m
    | Branches (Some ("cond" as m)) | Clauses (Some ("later" as m)) ->
        Printf.sprintf "all results of a %s must have the same type" m
    | Condition (Some m) | Branches (Some m) | Clauses (Some m) ->
        Printf.sprintf "in this use of `%s`" (f m)
    | Condition None -> "the condition of an if must be a Bool"
    | Branches None -> "both branches of an if must have the same type"
    | Key_access k -> Printf.sprintf "(:%s m) needs a map with the key :%s" k k
    | Changed_key k -> Printf.sprintf "this path goes through :%s, so the map needs it" k
    | Path_step ->
        "a step like this goes into a vector (by index) or a dictionary (by key)"
    | Path_key -> "this step is a vector's index (an Int) or a dictionary's key"
    | Kept_element -> "a change inside a vector or a dictionary keeps its elements' type"
    | Kept_type (n, forms) ->
        Printf.sprintf "`%s` keeps its type: %s cannot change it" n forms
    | Awaited -> "@ goes before a task"
    | Returned { origin = Some m; _ } -> Printf.sprintf "in this use of `%s`" (f m)
    | Returned { index; func = Some g; _ } ->
        Printf.sprintf "what this function gives back, as argument %d of `%s`" (index + 1)
          (f g)
    | Returned { index; _ } ->
        Printf.sprintf "what this function gives back, as argument %d" (index + 1)
    | Element -> "all elements of a vector must have the same type"
    | Pattern -> "a pattern must match the type of the value being matched"
    | Clauses None -> "all results of a match must have the same type"
    | Failure_clause -> "a clause of let gives what the rest of its body gives"
    | Recursion g -> Printf.sprintf "`%s` is used recursively with a different type" (f g)
    | Unquoted -> "~ inserts a Form, and ~@ inserts a [Form]"
    | Message -> "a file's handlers and views share one type of message"
    | View_html -> "a view in a page gives html"
    | View_pixels -> "a view in a window gives its pixels, a [U32]"
    | Written w -> Printf.sprintf "as written: `%s`" w
    | Untold n ->
        Printf.sprintf "what `%s` gives is decoded by a type written on its let" (f n)
  in
  (* Where first, then why. *)
  let headed =
    match error with
    | Inside _ | Key _ -> true
    | Mismatch (a, b) -> child a = child b && constrained a = None && constrained b = None
    | _ -> false
  in
  (* Both ends of the conflict: where this check fixed the type expected,
     if elsewhere, each with what it is. *)
  let d =
    match expected_at with
    | Some (s : Reader.span)
      when headed
           && (s.stop <= span.start || s.start >= span.stop)
           &&
           match site with
           | Argument { func = Some _; origin = None; _ }
           | Branches _ | Clauses _ | Element ->
               true
           | _ -> false ->
        d |> Diagnostic.mark s want |> Diagnostic.caption got
    | _ -> d
  in
  let d = if restated && headed then d else { d with notes = context :: d.notes } in
  let d =
    match site with
    | Argument { func = Some "macro/later-dropping"; _ } ->
        { d with message = "this task can fail, and `later` has no clause for it" }
    | _ -> d
  in
  let numbers, acting =
    match innermost error with
    | Mismatch (x, y) -> (
        match (zonk c x, zonk c y) with
        | Con (x, []), Con (y, []) -> (Num.is_name x && Num.is_name y && x <> y, false)
        | Fun (_, _, e), Fun (_, _, f) ->
            (false, e <> f && List.mem e [ plain; acts ] && List.mem f [ plain; acts ])
        | _ -> (false, false))
    | _ -> (false, false)
  in
  let d =
    if acting then note "a function that acts can't go where a plain one, ->, is taken" d
    else d
  in
  (* The rule for :why. *)
  Diagnostic.why
    (match (error, site) with
    | _, (Argument { origin = Some "@"; _ } | Returned { origin = Some "@"; _ }) ->
        "tasks-share-errors"
    | _, Returned { origin = Some "later"; _ }
    | _, Argument { func = Some "macro/later-dropping"; _ } ->
        "later"
    | (Missing_key _ | Extra_key _ | Recursive_row), _ -> "keys"
    | Occurs _, _ -> "infinite-type"
    | Outside _, _ -> "number-fits"
    | Held _, _ -> "buffer-held"
    | Arity _, _ -> "arity"
    | _ when versions <> None -> "redefinition"
    | Mismatch (a, b), _ when child a <> child b || child expected <> child found ->
        "html"
    | Mismatch (a, b), _ when constrained a <> None || constrained b <> None -> "compare"
    | _, (Path_step | Path_key | Kept_element | Changed_key _ | Key_access _) -> "paths"
    | _, Kept_type _ -> "changing-type"
    | _, Written _ -> "written-types"
    | _, Untold _ -> "decoding"
    | _, Failure_clause -> "let-clauses"
    | _, Unquoted -> "quasiquote"
    | _, Message -> "messages"
    | _, (View_html | View_pixels) -> "views"
    | _, Pattern -> "patterns"
    | _ when numbers -> "number-types"
    | _ when acting -> "bang"
    | _ -> "one-type")
    d

let unify_at c expected found span site =
  c.checking <- span;
  try unify c expected found
  with Unify e -> Diagnostic.fail (explain c e expected found span site)

(* A name that begins a group of names (task for task/map) lists the group. *)
let unknown env phase what name span candidates =
  let name = shown env name and candidates = List.map (shown env) candidates in
  let d = Diagnostic.make ~why:"unknown-name" phase span
            (Printf.sprintf "unknown %s `%s`" what name) in
  let d =
    match Diagnostic.suggest name candidates with
    | Some s -> Diagnostic.fix (Edit (span, Diagnostic.rename name s)) d
    | None -> d
  in
  let group = List.filter (String.starts_with ~prefix:(name ^ "/")) candidates in
  let shown = List.filteri (fun i _ -> i < 8) group in
  let more = List.length group - List.length shown in
  Diagnostic.fail
    (if group = [] then d
     else
       Diagnostic.note
         (Printf.sprintf "names starting with %s/: %s%s" name (String.concat ", " shown)
            (if more > 0 then Printf.sprintf ", and %d more" more else ""))
         d)

(* Whether a value of type [ty] holds a buffer. Vectors, dictionaries
   and tasks hold none, and functions hold none from outside. *)
let rec held c ty : Once.held =
  match resolve c ty with
  | Var v -> if snd (state c v) = None then Generic else Never
  | Con ("Vector", [ _; m ]) -> (
      match resolve c m with Var _ -> Either | m -> if m = unique then Surely else Never)
  | Con (("Dict" | "Task"), _) -> Never
  | Con (_, ts) -> List.fold_left (fun h t -> max h (held c t)) Never ts
  | Record r -> held c r
  | Row_extend (_, t, r) -> max (held c t) (held c r)
  | _ -> Never

let bang name = String.ends_with ~suffix:"!" name

(* The file's messages, which [message] must be; the first that is fully
   known fixes them. *)
let messages c message span =
  match c.messages with
  | Some m -> unify_at c (knowns c m) message span Message
  | None ->
      let rec known = function
        | Var _ | Gen _ -> false
        | Con (_, ts) -> List.for_all known ts
        | Fun (ps, r, _) -> List.for_all known (r :: ps)
        | Record r -> known r
        | Row_extend (_, t, r) -> known t && known r
        | Row_empty | Unknown _ -> true
      in
      let t = zonk c message in
      if known t then c.messages <- Some t

(* Whether [n], where it is used, is a parameter of a function around: calling
   one needs no !. *)
let parameter c n =
  match (List.assoc_opt n c.locals, List.assoc_opt n c.params) with
  | Some s, Some p -> s == p
  | _ -> false

(* Whether [ty] is a function that acts. *)
let acting c ty = match resolve c ty with Fun (_, _, e) -> resolve c e = acts | _ -> false

(* A name holding a function that acts ends in !. One written as a
   function says so itself. *)
let holds_action c (name : Ast.binding) (value : Ast.expr) ty =
  match value.kind with
  | Fn _ -> ()
  | _ when acting c ty && not (bang name.name) ->
      let n = shown c.env name.name in
      Diagnostic.fail
        (Diagnostic.make Type name.name_span
           (Printf.sprintf "`%s` holds a function that acts: name it `%s!`" n n)
        |> Diagnostic.note "a call that changes the file's names shows a !"
        |> Diagnostic.fix (Edit (name.name_span, fun _ -> Some (n ^ "!")))
        |> Diagnostic.why "bang")
  | _ -> ()

(* What acting where only reading is allowed says. *)
let read_only c span =
  let fail why message note =
    Diagnostic.fail (Diagnostic.make ~why Type span message |> Diagnostic.note note)
  in
  match c.place with
  | Macro_body ->
      fail "quasiquote" "a macro cannot change the file's names"
        "a macro runs while code is read, before the program does"
  | View_body ->
      fail "views" "a view only reads: it cannot change the file's names"
        "it is drawn after every change, so a change in it would set itself off again; \
         a button in it sends a message, and a handler makes the change"
  | In_fn { name = Some n; _ } when not (bang n) ->
      let n = shown c.env n in
      Diagnostic.fail
        (Diagnostic.make Type span
           (Printf.sprintf "`%s` changes the file's names: name it `%s!`" n n)
        |> Diagnostic.note "what changes the program's state is marked with !"
        |> Diagnostic.why "bang")
  | _ -> ()

(* A set!, update! or send! at [span]: the function it is in acts. *)
let changes_names c span =
  read_only c span;
  unify c c.acts acts

(* A call shows a ! if and only if it acts. *)
let shown_right c (k : call) =
  let f = Option.fold ~none:"" ~some:(shown c.env) k.callee in
  (* The fix adds or drops the ! at the call. *)
  let fail message note =
    let written, fixed = if k.shows then (f ^ "!", f) else (f, f ^ "!") in
    let d =
      Diagnostic.make Type k.at message |> Diagnostic.note note |> Diagnostic.why "bang"
    in
    Diagnostic.fail
      (if f = "" then d
       else Diagnostic.fix (Edit (k.at, Diagnostic.rename written fixed)) d)
  in
  let shows = "a call that changes the file's names shows a !" in
  match (resolve c k.action = acts, k.shows) with
  | true, false -> (
      match (k.callee, List.find_opt (fun (_, t) -> acting c t) k.given) with
      | None, _ ->
          fail "this call changes the file's names, but shows no !"
            "name the function first, with a !: (let jump! (:jump moves))"
      | Some _, Some ({ kind = Var g; _ }, _) ->
          let g = shown c.env g in
          fail (Printf.sprintf "`%s` acts here because `%s` does: write `%s!`" f g f)
            shows
      | Some _, Some _ ->
          fail
            (Printf.sprintf
               "`%s` acts here because the function given does: write `%s!`" f f)
            shows
      | Some _, None -> fail (Printf.sprintf "`%s` acts: write `%s!`" f f) shows)
  | false, true when k.added ->
      fail
        (Printf.sprintf "`%s!` changes nothing here: write `%s`" f f)
        (if k.passes then
           "it acts only when the function it is given does, and the call that gives one \
            shows the !"
         else "a ! marks a call that changes the file's names")
  | _ -> ()

(* At the end of a function: each call in it shows a ! if and only if it
   acts. If one acts, so does the function; otherwise it acts when the
   functions its calls act through do. *)
let settle c =
  let calls = List.rev c.calls in
  List.iter (shown_right c) calls;
  Option.iter
    (fun k ->
      read_only c k.at;
      unify c c.acts acts)
    (List.find_opt (fun k -> resolve c k.action = acts) calls);
  if resolve c c.acts <> acts then
    List.iter (fun k -> if resolve c k.action <> plain then unify c k.action c.acts) calls

(* A recording's types stand for the file's: its start, a map of the
   names the file's code changes, and its messages. *)
let recorded c span ty =
  let start = type_key c.env "vastra.browser/Start"
  and message = type_key c.env "vastra.browser/Message" in
  let base n = List.hd (List.rev (String.split_on_char '/' n)) in
  let rec go = function
    | Con (k, []) when k = start ->
        let names =
          Env.fold
            (fun n _ acc ->
              match Env.find_opt n c.env.vars with
              | Some s -> (n, knowns c s.ty) :: acc
              | None -> acc)
            c.env.changing []
        in
        (* The start keeps each by its own name, which names in two files can
           share: how it tells them apart is not decided. *)
        List.iter
          (fun (n, _) ->
            match List.find_opt (fun (m, _) -> m <> n && base m = base n) names with
            | Some (m, _) ->
                let what = "it keeps each name the program changes by its own name" in
                Diagnostic.fail
                  (Diagnostic.make ~why:"recording" Type span
                     (Printf.sprintf "a recording can't tell `%s` from `%s`"
                        (shown c.env n) (shown c.env m))
                  |> Diagnostic.note (what ^ ": rename one"))
            | None -> ())
          names;
        let names = List.map (fun (n, t) -> (base n, t)) names in
        Record (List.fold_left (fun row (k, t) -> Row_extend (k, t, row)) Row_empty names)
    | Con (k, []) when k = message -> (
        match c.messages with Some m -> knowns c m | None -> fresh c)
    | Con (n, args) -> Con (n, List.map go args)
    | Fun (ps, r, e) -> Fun (List.map go ps, go r, e)
    | Record r -> Record (go r)
    | Row_extend (k, t, r) -> Row_extend (k, go t, go r)
    | t -> t
  in
  go ty

let lookup c (e : Ast.expr) name =
  let span = e.span in
  (* A generic name is told the number types it is used at; a function's own
     name, inside it, those it was told. *)
  let use told = if told <> [] then e.typed <- Use told in
  let generic (s : scheme) =
    let fresh = fresh_vars ~from:name c s in
    let told = List.filteri (fun i _ -> told s.vars.(i)) (Array.to_list fresh) in
    later c (fun () -> use (List.map (num c) told));
    Option.iter
      (fun (g, otherwise) ->
        c.telling <- (fresh.(g), knowns c (substitute fresh otherwise), e) :: c.telling)
      s.told;
    knowns c (substitute fresh s.ty)
  in
  match List.assoc_opt name c.locals with
  | Some s when Option.fold c.self ~none:false ~some:(( == ) s) ->
      later c (fun () -> use (List.map (fun v -> Ast.Hidden v) (told_vars c s.ty)));
      s.ty
  | Some s ->
      (* Known to hold a buffer, a name from outside the function is refused
         now; Once refuses the others. *)
      if List.exists (fun (_, o) -> o == s) c.outside && held c s.ty = Surely then
        Once.from_outside name span c.origin;
      generic s
  | None when Env.mem name c.env.suspended ->
      let cause = Env.find name c.env.suspended in
      Diagnostic.fail
        (Diagnostic.make ~why:"redefinition" Name span
           (Printf.sprintf
              "`%s` cannot be used here: it depends on `%s`, which was just redefined \
               with a new type"
              (shown c.env name) (shown c.env cause))
        |> Diagnostic.note
             (Printf.sprintf
                "redefine `%s` in this submission too, or use it in the next one"
                (shown c.env name)))
  | None -> (
      match Env.find_opt name c.env.vars with
      | Some _ when c.plain <> None && Env.mem name c.env.changing ->
          Diagnostic.fail
            (Diagnostic.make ~why:"plain-reads-change" Type span
               (Printf.sprintf "`%s` changes %s: take it as a parameter"
                  (shown c.env name) (Env.find name c.env.changing))
            |> Diagnostic.note
                 (Printf.sprintf
                    "`%s` is a plain function, which sees no change; ! functions and \
                     handlers read the names that change"
                    (shown c.env (Option.get c.plain))))
      | Some s when String.starts_with ~prefix:"vastra.browser/" name ->
          recorded c span (generic s)
      | Some s -> generic s
      | None when String.starts_with ~prefix:"^" name ->
          Diagnostic.fail
            (Diagnostic.make ~why:"parallel" Name span
               (Printf.sprintf "`%s` has no parallel version"
                  (String.sub name 1 (String.length name - 1))))
      | None ->
          unknown c.env Name "name" name span
            (List.map fst c.locals @ List.map fst (Env.bindings c.env.vars)))

let with_locals c bindings f =
  let saved = c.locals in
  c.locals <- List.rev_append bindings c.locals;
  let result = f () in
  c.locals <- saved;
  result

(* A constructor's field types and result type, with fresh type parameters. *)
let constructor c name span =
  match Env.find_opt name c.env.ctors with
  | None ->
      unknown c.env Name "constructor" name span (List.map fst (Env.bindings c.env.ctors))
  | Some ty ->
      let def = Env.find ty c.env.types in
      let params = Array.init def.params (fun _ -> fresh c) in
      ( List.map (substitute params) (List.assoc name def.ctors),
        Con (ty, Array.to_list params) )

let rec infer_pattern c binds (p : Ast.pattern) =
  match p.pat with
  | PWild -> fresh c
  | PVar name ->
      let t = fresh c in
      binds := (name, mono t) :: !binds;
      c.matched <- (p, t) :: c.matched;
      t
  (* Floats cannot be matched. *)
  | PInt n ->
      let t = fresh ~constr:Integer c in
      literal c t n;
      t
  | PStr _ -> str
  | PBool _ -> bool
  | PCtor (name, args) ->
      let fields, result = constructor c name p.pat_span in
      if List.length fields <> List.length args then
        Diagnostic.fail
          (Diagnostic.make ~why:"arity" Type p.pat_span
             (Printf.sprintf "`%s` has %s, but the pattern gives %d" (shown c.env name)
                (Diagnostic.plural (List.length fields) "field")
                (List.length args)));
      List.iter2
        (fun field (arg : Ast.pattern) ->
          unify_at c field (infer_pattern c binds arg) arg.pat_span Pattern)
        fields args;
      result
  | PVector items ->
      let elem = fresh c in
      List.iter
        (fun (i : Ast.pattern) ->
          unify_at c elem (infer_pattern c binds i) i.pat_span Element)
        items;
      vector elem

let signature env key =
  if key = "true" || key = "false" then Some [ ("true", 0); ("false", 0) ]
  else
    Option.map
      (fun ty ->
        List.map
          (fun (k, fields) -> (k, List.length fields))
          (Env.find ty env.types).ctors)
      (Env.find_opt key env.ctors)

(* What Once needs of this check. *)
let found c : Once.found =
  {
    binding = (fun b -> List.assq b c.bound);
    pattern = (fun p -> List.assq p c.matched);
    got = (fun e -> List.assq e c.got);
    held = held c;
    no_buffer = (fun ty why -> bufferless c (Bufferless why) ty);
    reads =
      (fun f ->
        match Env.find_opt f c.env.vars with
        | Some s when not (List.mem_assoc f c.locals) -> s.reads
        | _ -> []);
    shown = shown c.env;
    line = c.line;
  }

(* Type syntax: Int, [a], (-> a b c), {:key T}. [var] resolves a lowercase name.
   An arrow says whether its function acts: ->! does, ->? when the
   functions given do. A plain -> [given] as an argument takes no action; one
   that gives a function is plain, and fits where an action could go:
   [plain] makes its variable. *)
let rec parse_type ?(given = false) ?(plain = fun () -> plain) env var
    (node : Reader.node) =
  let parse_type ?(given = given) = parse_type ~given ~plain env var in
  let fail message =
    Diagnostic.fail (Diagnostic.make ~why:"written-types" Syntax node.span message)
  in
  let named name args =
    let key = type_key env name in
    match Env.find_opt key env.types with
    | None ->
        unknown env Name "type" name node.span (List.map fst (Env.bindings env.types))
    | Some _ when key = "Vector" ->
        let inside = if args = [] then [ "Int" ] else List.map Reader.to_source args in
        fail (Printf.sprintf "a vector's type is written [%s]" (String.concat " " inside))
    | Some def when def.params <> List.length args ->
        Diagnostic.fail
          (Diagnostic.make ~why:"arity" Type node.span
             (Printf.sprintf "`%s` expects %s, but was given %d" (shown env name)
                (Diagnostic.plural def.params "type argument")
                (List.length args)))
    | Some { shape = Some t; _ } ->
        let args = Util.map_in_order (fun a -> parse_type a) args in
        substitute (Array.of_list args) (current env t)
    | Some _ -> (
        let args = Util.map_in_order (fun a -> parse_type a) args in
        match (key, args) with
        | "Buffer", [ a ] -> vector ~mode:unique a
        | _ -> Con (key, args))
  in
  match node.form with
  | Symbol name when Analyze.is_upper name -> named name []
  | Symbol name -> var name node.span
  | Vector [ a ] -> vector (parse_type a)
  | Vector _ -> fail "a vector's type has one type in it, as in [Int]"
  | List ({ form = Symbol ("->" | "->!" | "->?" as arrow); span; _ } :: (_ :: _ as parts))
    -> (
      let action =
        match arrow with
        | "->!" -> acts
        | "->?" -> var "->?" span
        | _ -> if given then Types.plain else plain ()
      in
      let parts = List.mapi (fun i p -> (i = List.length parts - 1, p)) parts in
      match
        List.rev
          (Util.map_in_order
             (fun (last, p) -> parse_type ~given:(if last then given else not given) p)
             parts)
      with
      | ret :: params -> Fun (List.rev params, ret, action)
      | [] -> fail "expected a type here")
  | List ({ form = Symbol name; _ } :: args) when Analyze.is_upper name -> named name args
  | Map entries ->
      let field ((k : Reader.node), v) =
        match k.form with
        | Keyword key -> (key, parse_type v)
        | _ -> fail "record type keys must be keywords"
      in
      (* {:k T | r}: these keys, and maybe others (r), as types are printed. *)
      let entries, tail =
        match List.rev entries with
        | ({ form = Symbol "|"; _ }, { form = Symbol r; span; _ }) :: rest ->
            (List.rev rest, var r span)
        | _ -> (entries, Row_empty)
      in
      Record
        (List.fold_right
           (fun (k, t) rest -> Row_extend (k, t, rest))
           (Util.map_in_order field entries)
           tail)
  | _ -> fail "expected a type here"

(* A written type: each lowercase name in it is a variable, which
   inference fills in. *)
let written_type c w =
  let vars = Hashtbl.create 2 in
  let var v _ =
    match Hashtbl.find_opt vars v with
    | Some t -> t
    | None ->
        let t = fresh c in
        Hashtbl.add vars v t;
        t
  in
  parse_type c.env var w

let json c = Con (type_key c.env "vastra.json/Json", [])

(* Data from outside, decoded by a let's written type: Json, or a
   JavaScript value. What it is called in errors, if it is one. *)
let outside c ty =
  let ty = resolve c ty in
  if ty = json c then Some "JSON"
  else if ty = Con (type_key c.env "vastra.js/Value", []) then Some "a JavaScript value"
  else None

(* Whether [ty] has no variable left. *)
let rec known c ty =
  match resolve c ty with
  | Var _ | Gen _ -> false
  | Con (_, ts) -> List.for_all (known c) ts
  | Fun (ps, r, a) -> List.for_all (known c) (a :: r :: ps)
  | Record r -> known c r
  | Row_extend (_, t, r) -> known c t && known c r
  | Row_empty | Unknown _ -> true

(* The written type [ty] as decoding reads it: fully known, so that there
   is something to check the data against. [w]: the type as written. *)
let describe c (w : Reader.node) ty : Shape.t =
  let fail message note =
    Diagnostic.fail (Diagnostic.make ~why:"decoding" Type w.span
                       message |> Diagnostic.note note)
  in
  let unknown () =
    fail
      (Printf.sprintf "`%s` is not fully known, so JSON can't be decoded to it"
         (Reader.to_source w))
      "a lowercase name, or | r in a map, could be anything: there is nothing to check \
       the data against"
  in
  let rec go ty : Shape.t =
    match resolve c ty with
    | Con ("Int", []) -> Int
    | Con ("Float", []) -> Float
    | Con ("String", []) -> String
    | Con ("Bool", []) -> Bool
    | Con ("Vector", [ a; m ]) when resolve c m = shared -> Vector (go a)
    | Con ("Option", [ a ]) -> Option (go a)
    | Record row -> Record (fields row)
    | t when t = json c -> Json
    | Con (k, _) when Env.mem k c.env.types && (Env.find k c.env.types).ctors <> [] ->
        words k
    | Var _ -> unknown ()
    | t ->
        fail
          (Printf.sprintf "JSON doesn't decode to %s" (show_with (namer_of c) (zonk c t)))
          "a written type decodes JSON to strings, numbers, booleans, vectors, maps, \
           Options, Json, and types whose constructors have outside words"
  (* Data decodes to a constructor only through its outside word. *)
  and words k =
    let def = Env.find k c.env.types in
    let word (ctor, fields) =
      let says message = Printf.sprintf message (shown c.env ctor) (shown c.env k) in
      match (fields, List.assoc_opt ctor def.words) with
      | _ :: _, _ ->
          fail
            (says "`%s` holds values, so JSON can't decode to `%s`")
            "a constructor holding values is decoded with vastra.decode"
      | [], None ->
          fail
            (says "`%s` has no outside word, so JSON can't decode to `%s`")
            "a constructor's word follows it: (type Gender Female \"female\" Male \
             \"male\")"
      | [], Some w -> (ctor, w)
    in
    Words (Util.map_in_order word def.ctors)
  and fields row =
    match resolve c row with
    | Row_extend (k, t, rest) ->
        let t = go t in
        (k, t) :: fields rest
    | Row_empty -> []
    | _ -> unknown ()
  in
  go ty

(* The type written on a name, checked against [ty]. A native whose answer it
   fixes is told it. *)
let written c name (w : Reader.node option) ty span =
  Option.iter
    (fun w ->
      let t = written_type c w in
      if outside c ty <> None && resolve c t <> resolve c ty then
        Diagnostic.fail
          (Diagnostic.make ~why:"decoding" Type span
             (Printf.sprintf "%s is decoded by a let of its own, with an (Err why) clause"
                (if outside c ty = Some "JSON" then "a Json value" else "a JavaScript value"))
          |> Diagnostic.note
               "data from outside can always be wrong: (let people::[Person] data \
                [(Err why) ...])");
      let waiting =
        if known c t then List.filter (fun (d, _, _) -> not (known c d)) c.telling else []
      in
      let site = Written (shown c.env name ^ "::" ^ Reader.to_source w) in
      unify_at c t ty span site;
      List.iter
        (fun ((d, _, (e : Ast.expr)) as native) ->
          if known c d then (
            e.typed <- Told_type (describe c w d);
            c.telling <- List.filter (( != ) native) c.telling))
        waiting)
    w

(* A native no written type told, whose answer a let decodes, gives what it
   does otherwise, as it would once the definition is checked. *)
let untold c subject =
  List.iter
    (fun ((d, otherwise, (e : Ast.expr)) as native) ->
      match (resolve c d, resolve c subject) with
      | Var a, Var b when a = b ->
          let f = match e.kind with Var f -> f | _ -> "" in
          unify_at c otherwise d e.span (Untold f);
          c.telling <- List.filter (( != ) native) c.telling
      | _ -> ())
    c.telling

(* A let whose written type isn't Json decodes a Json value: its clauses
   meet what decoding gives, a (Result String T). *)
let decoding c (e : Ast.expr) subject clauses =
  match clauses with
  | ({ Ast.pat = PCtor (success, [ { written = Some w; pat_span; _ } ]); _ }, _) :: _
    when untold c subject; outside c subject <> None ->
      let t = written_type c w in
      if resolve c t = resolve c subject then subject
      else (
        if success <> "Ok" then
          Diagnostic.fail
            (Diagnostic.make ~why:"decoding" Type pat_span
               (Printf.sprintf "decoding %s needs an (Err why) clause"
                  (Option.get (outside c subject)))
            |> Diagnostic.note "data from outside can always be wrong");
        e.typed <- Decodes (describe c w t);
        Con ("Result", [ str; t ]))
  | _ -> subject

(* The types written on a let's name, in its pattern. *)
let rec written_in c (p : Ast.pattern) =
  (match p.pat with
  | PVar n -> written c n p.written (List.assq p c.matched) p.pat_span
  | _ -> ());
  match p.pat with PCtor (_, ps) | PVector ps -> List.iter (written_in c) ps | _ -> ()

(* A map with [key], and what reading the key gives: an Option when it may be
   missing. *)
let keyed c key =
  let field = fresh c in
  let rest = fresh c in
  let value = if Util.may_miss key then Con ("Option", [ field ]) else field in
  (Record (Row_extend (key, field, rest)), value)

(* A type for the code that runs: a number still open is an Int, as for literals,
   unless a generic function is told it. *)
let as_written c t =
  map_type
    (function
      | Var v as ty -> (
          match Dynarray.get c.table v with
          | Unbound (_, Some (Integer | Number)) when not (List.mem v c.generic) -> int
          | _ -> ty)
      | ty -> ty)
    t

let rec infer c (e : Ast.expr) =
  let t = infer_kind c e in
  later c (fun () -> if e.typed = Untyped then e.typed <- Type (as_written c (zonk c t)));
  t

and infer_kind c (e : Ast.expr) =
  (* What an earlier check noted may have changed with a redefinition. *)
  e.typed <- Untyped;
  match e.kind with
  | Int n | Hex n ->
      let t = fresh ~constr:(match e.kind with Hex _ -> Integer | _ -> Number) c in
      literal c t n;
      later c (fun () -> e.typed <- Literal (num c t));
      t
  | Float _ -> float
  | Bool _ -> bool
  | Str _ -> str
  | Var name when Analyze.is_upper name -> (
      match constructor c name e.span with
      | [], result -> result
      | fields, result -> Fun (fields, result, fresh c))
  | Var name -> lookup c e name
  | Keyword key ->
      let map, value = keyed c key in
      Fun ([ map ], value, fresh c)
  | Vector items ->
      let elem = fresh c in
      List.iter (fun (i : Ast.expr) -> unify_at c elem (infer c i) i.span Element) items;
      c.got <- (e, elem) :: c.got;
      vector elem
  | Record fields ->
      let typed = Util.map_in_order (fun (k, v) -> (k, infer c v)) fields in
      (* Its keys, and maybe keys that may be missing, which it leaves out. *)
      let rest = fresh ~constr:(Optional None) c in
      Record (List.fold_right (fun (k, t) rest -> Row_extend (k, t, rest)) typed rest)
  | Get { key; record } ->
      let record_ty = infer c record in
      let map, value = keyed c key in
      unify_at c map record_ty record.span (Key_access key);
      value
  | Read { target; path } ->
      (* An Option when a step can be missing: an index, a dictionary key, or
         a key that may be missing. Other keys cannot be missing; the
         types rule it out. *)
      let found = read_at c (infer c target) path in
      c.got <- (e, found) :: c.got;
      if List.exists (function Ast.At _ -> true | Key (k, _) -> Util.may_miss k) path
      then
        Con ("Option", [ found ])
      else found
  | Set { target; path; value } ->
      change_at c (infer c target) path ~adds:true ~last:value (fun _ -> infer c value)
  | Update { target; path; func } ->
      change_at c (infer c target) path ~adds:false ~last:func (fun old ->
          let result = fresh c in
          unify_at c
            (Fun ([ old ], result, plain))
            (infer c func) func.span
            (Argument
               { index = List.length path + 1; func = Some "update"; origin = None });
          result)
  | Change { target = { kind = Var name; _ } as target; value } ->
      if List.mem_assoc name c.locals then
        Diagnostic.fail
          (Diagnostic.make ~why:"set-names" Type target.span
             (Printf.sprintf
                "set! changes the file's names, and `%s` is this function's own" name)
          |> Diagnostic.note (Printf.sprintf "change it with (set %s ...)" name));
      changes_names c e.span;
      (match Env.find_opt name c.env.vars with
      | Some s when not (one_type s) ->
          Diagnostic.fail
            (Diagnostic.make ~why:"changing-type" Type target.span
               (Printf.sprintf "set! cannot change `%s`: its type, %s, is not fully known"
                  (shown c.env name)
                  (Types.show_scheme ~plain:true ~shown:(shown c.env) s))
            |> Diagnostic.note
                 "a name set! changes holds one type, which its let can say: \
                  (let log::[String] [])")
      | _ -> ());
      let old = close c (lookup c target name) in
      let ty =
        match value.kind with
        | Set { target; path; value = last } ->
            change_at c (infer c target) path ~adds:false ~last (fun _ -> infer c last)
        | _ -> infer c value
      in
      unify_at c old ty value.span (Kept_type (shown c.env name, "set! and update!"));
      unit
  | Change _ -> Diagnostic.fail (Diagnostic.make ~why:"set-names" Syntax e.span
                                   "set! changes a name")
  | Send message ->
      changes_names c e.span;
      let ty = infer c message in
      if resolve c ty = Con (type_key c.env "vastra.window/Event", []) then
        Diagnostic.fail
          (Diagnostic.make ~why:"messages" Type message.span
             "a window's events come only from the window"
          |> Diagnostic.note "send! sends the file's own messages");
      messages c ty message.span;
      unit
  | Fn lambda ->
      if e.origin <> Some "@" then c.making <- Ast.references e @ c.making;
      infer_fn ?origin:e.origin c lambda
  | Await _ ->
      Diagnostic.fail
        (Diagnostic.make ~why:"quasiquote" Syntax e.span
           "@ runs a task, and a macro's code cannot run tasks")
  | Task_of x -> (
      let ty = infer c x in
      let result = fresh c in
      let task = Con ("Task", [ fresh c; result ]) in
      match resolve c ty with
      | Con ("Task", _) ->
          unify_at c task ty x.span Awaited;
          task
      (* A number, comparable or equatable type is not a task. *)
      | Var v when snd (state c v) = None ->
          unify_at c task ty x.span Awaited;
          task
      | other ->
          Diagnostic.fail
            (Diagnostic.make ~why:"task-run-by-at" Type x.span
               ("@ goes before a task, not a value of type "
               ^ show_with (namer_of c) (zonk c other))))
  | Run task ->
      let result = fresh c in
      unify_at c (Con ("Task", [ fresh c; result ])) (infer c task) task.span Awaited;
      result
  | Let { bindings; body; how } -> let_ c ~how e bindings body
  (* A par/let's bindings use none of each other's names (Analyze). *)
  | Par_let { bindings; body } -> let_ c ~how:Names e bindings body
  | If { condition; then_branch; else_branch } ->
      unify_at c bool (infer c condition) condition.span (Condition e.origin);
      let t = infer c then_branch in
      let e' = infer c else_branch in
      unify_at c t e' else_branch.span (Branches e.origin);
      t
  | Match { scrutinee; clauses } ->
      let failures = e.origin = Some "let" in
      let site = if failures then Failure_clause else Clauses e.origin in
      let subject = infer c scrutinee in
      let subject = if failures then decoding c e subject clauses else subject in
      let result = ref None in
      List.iter
        (fun ((p : Ast.pattern), (body : Ast.expr)) ->
          let binds = ref [] in
          unify_at c subject (infer_pattern c binds p) p.pat_span Pattern;
          written_in c p;
          let t = with_locals c (List.rev !binds) (fun () -> infer c body) in
          match !result with
          | None -> result := Some t
          | Some r -> unify_at c r t body.span site)
        clauses;
      (* A handler's match ends with _, so that an event it doesn't take is None. *)
      if e.origin <> Some "on" then
        Exhaustive.check
          ~clauses:(if failures then `Let else `Match)
          (signature c.env) (List.map fst clauses) e.span;
      Option.get !result
  | Call { func; args } -> infer_call c func args e.span
  | Quote _ -> con "Form"
  | Quasi q ->
      let rec template = function
        | Ast.Leaf _ | Gensym _ -> ()
        | Unquote (x : Ast.expr) -> unify_at c (con "Form") (infer c x) x.span Unquoted
        | Coll (_, items) ->
            List.iter
              (function
                | Ast.Item q -> template q
                | Splice (x : Ast.expr) ->
                    unify_at c
                      (vector (con "Form"))
                      (infer c x) x.span Unquoted)
              items
      in
      template q;
      con "Form"

and let_ c ~how (e : Ast.expr) bindings body =
  let saved = c.locals in
  List.iter
    (fun ((b : Ast.binding), (value : Ast.expr)) ->
      c.level <- c.level + 1;
      let making = c.making in
      c.making <- [];
      (match value.kind with Fn _ -> c.naming <- Some b.name | _ -> ());
      let ty =
        match how with
        | Changes ->
            let ty = changed c e b value in
            Analyze.unread b.name e.span body;
            ty
        | Recursive ->
            (* Within its body its name is monomorphic, as a top-level one's is. *)
            let self = mono (fresh c) in
            let ty = with_locals c [ (b.name, self) ] (fun () -> infer c value) in
            unify_at c self.ty ty b.name_span (Recursion b.name);
            ty
        | Names -> infer c value
      in
      written c b.name b.written ty value.span;
      holds_action c b value ty;
      let made = c.making in
      c.making <- made @ making;
      c.level <- c.level - 1;
      (* What a local function uses twice holds no buffer, in each use. *)
      (match value.kind with
      | Fn _ ->
          let self = if how = Recursive then Some b.name else None in
          ignore (Once.check ?self (found c) value);
          generic c value ty
      | _ -> monomorphic c ty);
      c.bound <- (b, ty) :: c.bound;
      let scheme = generalize c ty in
      c.made <- (scheme, made) :: c.made;
      c.locals <- (b.name, scheme) :: c.locals)
    bindings;
  let ty = infer c body in
  c.locals <- saved;
  ty

(* A set or update line changes a name of its own function, keeping its
   type, so it adds no key; and no function made since holds the name, which
   would keep the old one. *)
and changed c (line : Ast.expr) (b : Ast.binding) (value : Ast.expr) =
  let old =
    match List.assoc_opt b.name c.locals with
    | Some s when not (List.exists (fun (_, o) -> o == s) c.around) -> s
    | Some _ ->
        Diagnostic.fail
          (Diagnostic.make ~why:"set-names" Type b.name_span
             (Printf.sprintf "set cannot change `%s`: it is named outside this function"
                b.name)
          |> Diagnostic.note
               "a function changes only its own names: its parameters and lets")
    | None ->
        Diagnostic.fail
          (Diagnostic.make ~why:"set-names" Type b.name_span
             (Printf.sprintf
                "set changes this function's own names, and `%s` is the file's"
                (shown c.env b.name))
          |> Diagnostic.note "a ! function changes the file's names, with set!")
  in
  let rec since = function
    | (n, s) :: rest when s != old -> (n, s) :: since rest
    | _ -> []
  in
  List.iter
    (fun (n, s) ->
      match List.assq_opt s c.made with
      | Some uses when List.mem b.name uses && holds_function c s.ty ->
          Diagnostic.fail
            (Diagnostic.make ~why:"set-names" Type line.span
               (Printf.sprintf "`%s` holds `%s`, and would keep the old one" n b.name)
            |> Diagnostic.note
                 (Printf.sprintf "give `%s` to `%s` as a parameter instead" b.name n))
      | _ -> ())
    (since c.locals);
  let ty =
    match value.kind with
    | Set { target; path; value = last } ->
        change_at c (infer c target) path ~adds:false ~last (fun _ -> infer c last)
    | _ -> infer c value
  in
  unify_at c (instantiate c old) ty value.span (Kept_type (b.name, "set and update"));
  ty

(* Whether a value of type [ty] may hold a function: a task holds what it runs. *)
and holds_function c ty =
  match resolve c ty with
  | Fun _ | Con ("Task", _) -> true
  | Con (_, ts) -> List.exists (holds_function c) ts
  | Record r -> holds_function c r
  | Row_extend (_, t, r) -> holds_function c t || holds_function c r
  | _ -> false

(* The record must already have [key] (of type [old]); returns its row. *)
(* The type of [ty] once what is at [path] becomes [change old]. With
   [adds] (set), a map key missing at the last step is added, where the map's
   keys are all known; in generic code the key must be there, since adding
   would need to know it is not. *)
and change_at c ty path ~adds ~(last : Ast.expr) change =
  let rec has_key row key =
    match resolve c row with
    | Row_extend (k, _, rest) -> k = key || has_key rest key
    | _ -> false
  (* Whether [row] can't hold [key] unseen: a map written out has all its keys
     but those that may be missing. *)
  and closed row key =
    match resolve c row with
    | Row_extend (_, _, rest) -> closed rest key
    | Row_empty -> true
    | Var v -> (
        match snd (state c v) with
        | Some (Optional _) -> not (Util.may_miss key)
        | _ -> false)
    | _ -> false
  in
  match path with
  | [] -> change ty
  | Ast.Key (key, span) :: rest -> (
      no_key_into_collection c ty key span;
      match resolve c ty with
      | Record row when adds && rest = [] && closed row key && not (has_key row key) ->
          Record (replace_field c row key (change (fresh c)))
      | _ ->
          let old = field_at c ty key span in
          let row = match resolve c ty with Record row -> row | other -> other in
          Record (replace_field c row key (change_at c old rest ~adds ~last change)))
  | Ast.At index :: rest ->
      let elem = element_at c ty index in
      unify_at c elem (change_at c elem rest ~adds ~last change) last.span Kept_element;
      ty

(* The type of what [path] reaches in [ty], for get. *)
and read_at c ty path =
  match path with
  | [] -> ty
  | Ast.Key (key, span) :: rest ->
      no_key_into_collection c ty key span;
      read_at c (field_at c ty key span) rest
  | Ast.At index :: rest -> read_at c (element_at c ty index) rest

(* Steps of a path, shared by get, set and update. A keyword cannot step
   into a vector or a dictionary. *)
and no_key_into_collection c ty key span =
  let fail kind step =
    Diagnostic.fail
      (Diagnostic.make ~why:"paths" Type span
         (Printf.sprintf "a step into a %s is %s, not a key like :%s" kind step key))
  in
  match resolve c ty with
  | Con ("Vector", [ _; m ]) ->
      fail (if resolve c m = unique then "buffer" else "vector") "an index (an Int)"
  | Con ("Dict", _) -> fail "dictionary" "one of its keys"
  | _ -> ()

(* The type of [key] in the map [ty], which must have it. *)
and field_at c ty key span =
  let field = fresh c in
  unify_at c (Record (Row_extend (key, field, fresh c))) ty span (Changed_key key);
  field

(* The type of an element of the vector or dictionary [ty], with [index]
   checked as its index or key. *)
and element_at c ty (index : Ast.expr) =
  let key, elem =
    match resolve c ty with
    | Con ("Dict", [ k; v ]) -> (k, v)
    | Record _ ->
        Diagnostic.fail
          (Diagnostic.make ~why:"paths" Syntax index.span
             "a map's key in a path is written as a keyword, like :name")
    | _ ->
        let elem = fresh ~constr:(Bufferless "a vector cannot hold a buffer") c in
        unify_at c (vector ~mode:(fresh c) elem) ty index.span Path_step;
        (int, elem)
  in
  unify_at c key (infer c index) index.span Path_key;
  elem

(* [row] with [key]'s type replaced, keeping the keys' order. *)
and replace_field c row key ty =
  match resolve c row with
  | Row_extend (k, _, rest) when k = key -> Row_extend (k, ty, rest)
  | Row_extend (k, f, rest) -> Row_extend (k, f, replace_field c rest key ty)
  | other -> Row_extend (key, ty, other)

(* [expected]: the parameter and result types where the function is passed, so
   a mistake in its body is reported in the body. *)
and infer_fn ?expected ?origin c (l : Ast.lambda) =
  let params =
    match expected with
    | Some (types, _, _) ->
        List.map2 (fun (p : Ast.binding) t -> (p.name, t)) l.params types
    | None -> Util.map_in_order (fun (p : Ast.binding) -> (p.name, fresh c)) l.params
  in
  List.iter2
    (fun (p : Ast.binding) (_, t) ->
      written c p.name p.written t p.name_span;
      c.bound <- (p, t) :: c.bound)
    l.params params;
  let outside = c.outside and origin' = c.origin and around = c.around in
  let place = c.place and plain = c.plain in
  let acted = c.acts and calls = c.calls and params_around = c.params in
  c.acts <- fresh c;
  c.calls <- [];
  let schemes = List.map (fun (n, t) -> (n, mono t)) params in
  c.outside <- c.locals;
  (* A function @ makes runs when the task does, as part of the one written. *)
  (match (origin, c.place) with
  | Some "@", In_fn f -> c.place <- In_fn { f with waiting = true }
  | Some "@", _ -> ()
  (* A handler's body and a view are top-level code. *)
  | Some ("on" | "view"), _ ->
      c.around <- c.locals;
      c.place <- (if origin = Some "on" then Top else View_body);
      c.plain <- None
  | _ ->
      let name = c.naming in
      c.naming <- None;
      c.around <- c.locals;
      c.place <- In_fn { name; waiting = false };
      (* Calling a parameter needs no !: the call that gives it shows one. *)
      c.params <- schemes @ c.params;
      Option.iter (fun n -> c.plain <- (if bang n then None else Some n)) name);
  c.origin <- origin;
  let body = with_locals c schemes (fun () -> infer c l.body) in
  settle c;
  let fn_acts = c.acts in
  c.acts <- acted;
  c.calls <- calls;
  c.params <- params_around;
  c.place <- place;
  c.plain <- plain;
  c.outside <- outside;
  c.around <- around;
  c.origin <- origin';
  Option.iter
    (fun (_, result, reason) -> unify_at c result body l.body.span reason)
    expected;
  Fun (List.map snd params, body, fn_acts)

and infer_call c (func : Ast.expr) args span =
  let func_ty = infer c func in
  let name = match func.kind with Var n -> Some n | _ -> None in
  let ret = call_type c func func_ty name args span in
  (match (name, args) with
  | Some ("vastra.js/message*" | "vastra.js/receive*"), given :: _ ->
      sent c func func_ty given
  | _ -> ());
  (match resolve c func_ty with
  | Fun (params, _, action) ->
      let added = func.origin = Some "!" in
      let given (a : Ast.expr) = match a.kind with Var n -> parameter c n | _ -> false in
      let shows =
        match name with
        (* Calling a parameter needs no !: the call that gives it shows one. *)
        | Some n -> bang n || added || parameter c n
        | None -> false
      in
      let passes = List.exists given args in
      let given = List.combine args params in
      let call = { action; at = span; shows; added; passes; callee = name; given } in
      c.calls <- call :: c.calls
  | _ -> ());
  ret

(* What JavaScript may send the natives of js/message and js/receive: the
   file's messages, a constructor's values decoded as a let decodes them. They
   are told the constructor [given] makes, or every one of the type it gives. *)
and sent c (func : Ast.expr) func_ty (given : Ast.expr) =
  let made = match resolve c func_ty with Fun (f :: _, _, _) -> resolve c f | t -> t in
  let params, message = match made with Fun (ps, r, _) -> (ps, r) | t -> ([], t) in
  let refuse what example =
    Diagnostic.fail
      (Diagnostic.make ~why:"messages" Type given.span (what ^ " of the file's messages")
      |> Diagnostic.note example)
  in
  let values (ctor, types) =
    let form = Reader.Symbol (shown c.env ctor) in
    (ctor, List.map (describe c { form; span = given.span; origin = None }) types)
  in
  let shape =
    match (func.kind, given.kind, resolve c message) with
    | Var "vastra.js/message*", Var ctor, _ when Env.mem ctor c.env.ctors ->
        messages c message given.span;
        Shape.Message [ values (ctor, params) ]
    | Var "vastra.js/message*", _, _ ->
        refuse "js/message takes a constructor" "(js/message Picked [(Err why) ...])"
    | _, _, Con (k, _) when (Env.find k c.env.types).ctors <> [] ->
        messages c message given.span;
        Message (List.map values (Env.find k c.env.types).ctors)
    | _ -> refuse "js/receive takes the type" "(js/receive Msg [(Err why) ...])"
  in
  func.typed <- Told_type shape

and call_type c (func : Ast.expr) func_ty name args span =
  (* A ! added to the call is no macro's. *)
  let origin = if func.origin = Some "!" then None else func.origin in
  let check params type_of =
    if List.length params <> List.length args then
      Diagnostic.fail
        (Diagnostic.make ~why:"arity" Type span
           (Printf.sprintf "%s expects %s, but was given %d"
              (match name with
              | Some n -> "`" ^ shown c.env n ^ "`"
              | None -> "this function")
              (Diagnostic.plural (List.length params) "argument")
              (List.length args)));
    List.iteri
      (fun index (param, (arg : Ast.expr)) ->
        unify_at c param (type_of index param arg) arg.span
          (Argument { index; func = name; origin }))
      (List.combine params args)
  in
  match resolve c func_ty with
  | Fun (params, ret, _) ->
      (* In order: a function given where a function is expected is checked
         knowing its parameters' types, as far as the earlier arguments tell. *)
      check params (fun index param (arg : Ast.expr) ->
          match (arg.kind, resolve c param) with
          | Fn l, Fun (types, result, _) when List.length types = List.length l.params ->
              let origin = if arg.origin <> None then arg.origin else origin in
              infer_fn
                ~expected:(types, result, Returned { index; func = name; origin })
                ?origin:arg.origin c l
          | _ -> infer c arg);
      ret
  (* A number, comparable or equatable type is not a function. *)
  | Var v when snd (state c v) = None -> (
      let arg_tys = Util.map_in_order (infer c) args in
      (* The arguments may have told what the function is. *)
      match resolve c func_ty with
      | Fun (params, ret, _) ->
          check params (fun index _ _ -> List.nth arg_tys index);
          ret
      | _ ->
          let ret = fresh c in
          unify_at c (Fun (arg_tys, ret, fresh c)) func_ty func.span (Callee name);
          ret)
  (* A task is run with @, not called: (clock/now) is @clock/now. *)
  | Con ("Task", _) ->
      let what =
        Option.fold name ~none:"this" ~some:(fun n -> "`" ^ shown c.env n ^ "`")
      in
      let unwrap text =
        let n = String.length text in
        if args = [] && n > 2 && text.[0] = '(' && text.[n - 1] = ')' then
          Some ("@" ^ String.sub text 1 (n - 2))
        else None
      in
      Diagnostic.fail
        (Diagnostic.make Type func.span (what ^ " is a task, not a function")
        |> Diagnostic.note "a task gives its value where @ runs it"
        |> Diagnostic.fix (Edit (span, unwrap))
        |> Diagnostic.why "task-run-by-at")
  | other ->
      let shown = show_with (namer_of c) (zonk c other) in
      Diagnostic.fail
        (Diagnostic.make ~why:"one-type" Type func.span
           ("this is not a function; it has type " ^ shown))

(* A native's type: every lowercase name is a variable; integer, number,
   comparable and equatable (optionally followed by digits) are constrained
   ones, and so is child, a child of the html (Html msg). *)
let native_scheme env (node : Reader.node) =
  let vars = ref [] in
  let rec var name span =
    match List.assoc_opt name !vars with
    | Some (g, _) -> Gen g
    | None ->
        let digits = ref (String.length name) in
        while !digits > 0 && name.[!digits - 1] >= '0' && name.[!digits - 1] <= '9' do
          decr digits
        done;
        let base = String.sub name 0 !digits in
        let constr =
          if base = "child" then
            Some (Child (Con (type_key env "vastra.html/Html", [ var "msg" span ])))
          else
            List.assoc_opt base
              [
                ("integer", Integer);
                ("number", Number);
                ("comparable", Comparable);
                ("equatable", Equatable);
              ]
        in
        let g = List.length !vars in
        vars := (name, (g, constr)) :: !vars;
        Gen g
  in
  (* A parameter the native only reads is written &T. *)
  let node, reads =
    match node.form with
    | List (({ form = Symbol ("->" | "->!" | "->?"); _ } as arrow) :: parts) ->
        let rec strip i = function
          | ({ Reader.form = Symbol "&"; _ } : Reader.node) :: p :: rest ->
              let ps, rs = strip (i + 1) rest in
              (p :: ps, i :: rs)
          | p :: rest ->
              let ps, rs = strip (i + 1) rest in
              (p :: ps, rs)
          | [] -> ([], [])
        in
        let parts, reads = strip 0 parts in
        ({ node with form = List (arrow :: parts) }, reads)
    | _ -> (node, [])
  in
  let arrows = ref 0 in
  let plain () =
    incr arrows;
    var ("->" ^ string_of_int !arrows) node.span
  in
  (* (Told T): what the type written on a let tells the native, else T. *)
  let told = ref None in
  let rec untold (n : Reader.node) =
    match n.form with
    | List [ { form = Symbol "Told"; _ }; t ] ->
        told := Some t;
        { n with form = Symbol "told" }
    | List items -> { n with form = List (List.map untold items) }
    | _ -> n
  in
  let ty = parse_type ~plain env var (untold node) in
  let told =
    Option.map
      (fun t ->
        let g = match var "told" node.span with Gen g -> g | _ -> assert false in
        (g, parse_type ~plain env var t))
      !told
  in
  let a = Array.make (List.length !vars) None in
  List.iter (fun (_, (g, k)) -> a.(g) <- k) !vars;
  (* Vectors, buffers, dictionaries and tasks hold no buffers. *)
  let rec inside why = function
    | Gen g -> if a.(g) = None then a.(g) <- Option.map (fun w -> Bufferless w) why
    | Con ("Vector", [ t; _ ]) -> inside (Some "a vector cannot hold a buffer") t
    | Con ((("Dict" | "Task") as n), ts) ->
        let kind = if n = "Dict" then "dictionary" else "task" in
        List.iter (inside (Some ("a " ^ kind ^ " cannot hold a buffer"))) ts
    | Con (_, ts) -> List.iter (inside why) ts
    | Fun (ps, r, _) -> List.iter (inside None) (r :: ps)
    | Record r -> inside why r
    | Row_extend (_, t, r) ->
        inside why t;
        inside why r
    | _ -> ()
  in
  inside None ty;
  { vars = a; ty; holds = []; reads; told }

(* [name]'s definition, kept under [key]. A type is equatable unless a field
   holds a function; parameters count as equatable. *)
let new_type env key (name : Ast.binding) params (ctors : Ast.ctor list) shape =
  let index = List.mapi (fun i (p : Ast.binding) -> (p.name, i)) params in
  let var v span =
    match List.assoc_opt v index with
    | Some i -> Gen i
    | None ->
        Diagnostic.fail
          (Diagnostic.make ~why:"unknown-name" Name span
             (Printf.sprintf "unknown type variable `%s`" v)
          |> Diagnostic.note
               (Printf.sprintf "declare it as a parameter: (type (%s ... %s) ...)"
                  (shown env name.name) v))
  in
  let self = primitive (List.length params) in
  let env' = { env with types = Env.add key self env.types } in
  let parsed =
    Util.map_in_order
      (fun (c : Ast.ctor) ->
        if Env.mem c.ctor_name env.ctors then
          Diagnostic.fail
            (Diagnostic.make ~why:"defined-once" Type c.ctor_span
               (Printf.sprintf "the constructor `%s` is already defined"
                  (shown env c.ctor_name)));
        (c.ctor_name, Util.map_in_order (parse_type ~given:true env' var) c.fields))
      ctors
  in
  (* Without its own name: a map can't hold itself. *)
  let shape = Option.map (parse_type ~given:true env var) shape in
  let rec equatable = function
    | Gen _ -> true
    | Con (n, args) ->
        (n = key || (Env.find n env'.types).equatable)
        && List.for_all equatable args
    | Record r -> equatable r
    | Row_extend (_, f, rest) -> equatable f && equatable rest
    | Fun _ -> false
    | _ -> true
  in
  (* A type without constructors is opaque (its values come from natives): not equatable. *)
  let def =
    {
      self with
      shape;
      ctors = parsed;
      words =
        List.filter_map
          (fun (c : Ast.ctor) -> Option.map (fun w -> (c.ctor_name, w)) c.word)
          ctors;
      equatable =
        parsed <> [] && List.for_all (fun (_, fs) -> List.for_all equatable fs) parsed;
    }
  in
  {
    env with
    types = Env.add key def env.types;
    ctors = List.fold_left (fun m (k, _) -> Env.add k key m) env.ctors parsed;
  }

(* [env] without the current version of [name]'s constructors. *)
let without_ctors env name =
  let key = type_key env name in
  { env with ctors = Env.filter (fun _ t -> t <> key) env.ctors }

(* Whether [name] is defined already, as something else than this definition.
   The same definition again (a file submitted twice) changes nothing. *)
let changes env (name : Ast.binding) params ctors shape =
  let key = type_key env name.name in
  match Env.find_opt key env.types with
  | None -> false
  | Some old ->
      let env = { (without_ctors env name.name) with types = Env.remove key env.types } in
      Env.find_opt key (new_type env key name params ctors shape).types <> Some old

(* A definition that changes a type is a new version of it. *)
let define_type env (name : Ast.binding) params ctors shape =
  if not (Env.mem name.name env.types) then new_type env name.name name params ctors shape
  else if not (changes env name params ctors shape) then env
  else
    let v = 1 + Option.value (Env.find_opt name.name env.type_versions) ~default:0 in
    let env = without_ctors env name.name in
    let env = { env with type_versions = Env.add name.name v env.type_versions } in
    new_type env (type_key env name.name) name params ctors shape

(* A new unknown of [owner]'s. *)
let unknown c owner constr =
  let u = Ints.cardinal c.unknowns in
  c.unknowns <- Ints.add u (Open constr) c.unknowns;
  Unknown (u, owner)


(* [ty] as the session keeps it: the names' unknowns as such, and each
   variable left, a new unknown of [owner]'s. *)
let kept c owner ty =
  map_type
    (function
      | Var v ->
          let u = unknown c owner (snd (state c v)) in
          Dynarray.set c.table v (Link u);
          u
      | t -> t)
    (zonk ~lazily:true c (close c ty))

(* What an empty vector, an empty dictionary or None leaves open in a name's
   starting value waits for its uses: a variable whose every place is in one
   of them, outside any function. *)
let wait c owner ty =
  let places = ref [] in
  let rec go fn ok ty =
    match resolve c ty with
    | Var v when level_of c v > c.level -> places := (v, ok && not fn) :: !places
    | Con (("Vector" | "Dict" | "Option"), args) -> List.iter (go fn true) args
    | Con (_, args) -> List.iter (go fn false) args
    | Fun (ps, r, _) -> List.iter (go true false) (r :: ps)
    | Record r -> go fn false r
    | Row_extend (_, t, r) ->
        go fn false t;
        go fn false r
    | _ -> ()
  in
  go false false ty;
  List.iter
    (fun (v, _) ->
      let waits = List.for_all (fun (w, ok) -> w <> v || ok) !places in
      if resolve c (Var v) = Var v && waits then
        Dynarray.set c.table v (Link (unknown c owner (snd (state c v)))))
    (List.rev !places)

(* [ty] with each unknown its uses fixed replaced by its type. *)
let rec resolved (env : env) ty =
  map_type
    (function
      | Unknown (u, _) as t -> (
          match Ints.find u env.unknowns with
          | Fixed (t, _) -> resolved env t
          | Open _ -> t)
      | t -> t)
    ty

(* Whether [f] unifies; if not, nothing changed. *)
let tentatively c f =
  let table = Dynarray.copy c.table and holds = Hashtbl.copy c.holds in
  match f () with
  | () -> true
  | exception Unify _ ->
      Dynarray.truncate c.table (Dynarray.length table);
      Dynarray.iteri (Dynarray.set c.table) table;
      Hashtbl.reset c.holds;
      Hashtbl.iter (Hashtbl.replace c.holds) holds;
      false

(* A name defined again keeps its old type, with what its uses fixed, as far
   as [ty], its starting value's, fits it: under each key the two share, so
   that a key whose type did not change keeps its value. *)
let rec share c ty old =
  let rec fields row =
    match resolve c row with Row_extend (k, t, rest) -> (k, t) :: fields rest | _ -> []
  in
  if tentatively c (fun () -> unify c ty old) then old
  else
    match (resolve c ty, resolve c old) with
    | Record r, Record o ->
        let rec row r =
          match resolve c r with
          | Row_extend (k, t, rest) ->
              let old = List.assoc_opt k (fields o) in
              let t = Option.fold old ~none:t ~some:(share c t) in
              Row_extend (k, t, row rest)
          | r -> r
        in
        Record (row r)
    | _ -> ty

(* Each vector or buffer in [ty], outside functions, a vector: at the top
   level nothing comes after to make it a buffer. *)
let rec as_vectors c ty =
  match resolve c ty with
  | Con ("Vector", [ a; m ]) ->
      (match resolve c m with Var _ -> unify c m shared | _ -> ());
      as_vectors c a
  | Con (_, ts) -> List.iter (as_vectors c) ts
  | Record r -> as_vectors c r
  | Row_extend (_, t, r) ->
      as_vectors c t;
      as_vectors c r
  | _ -> ()

(* A handler, of type (-> event (Option (-> r))): it takes window events,
   or the messages the file's page handlers and views share. It cannot fail,
   and ends with a value, or with a task its @s made. Gives whether it takes
   window events, and the messages. *)
let handles c env (handler : Ast.expr) ~waits ty =
  let fail span message note =
    Diagnostic.fail (Diagnostic.make ~why:"messages" Type span
                       message |> Diagnostic.note note)
  in
  (* The fix puts @ before the handler's last form. *)
  let unrun () =
    let run text =
      match Reader.read_all text with
      | Ok [ { form = List items; _ } ] ->
          let last = (List.nth items (List.length items - 1)).span.start in
          let rest = String.sub text last (String.length text - last) in
          Some (String.sub text 0 last ^ "@" ^ rest)
      | _ -> None
    in
    Diagnostic.fail
      (Diagnostic.make Type handler.span "this handler ends with a task it doesn't run"
      |> Diagnostic.note "a task runs where @ is written before it"
      |> Diagnostic.fix (Edit (handler.span, run))
      |> Diagnostic.why "task-run-by-at")
  in
  match resolve c ty with
  | Fun ([ event ], option, _) ->
      (match resolve c option with
      | Con ("Option", [ run ]) -> (
          match resolve c run with
          | Fun ([], r, _) -> (
              match resolve c r with
              | Con ("Task", [ e; a ]) when waits -> (
                  (try unify c e (con "Never")
                   with Unify _ ->
                     fail handler.span
                       ("a handler cannot fail, and this one can fail with "
                       ^ show_with (namer_of c) (zonk c e))
                       "take each failure in a let's clause, as [(Err why) ...]");
                  match resolve c a with
                  | Con ("Task", _) -> unrun ()
                  | _ -> ())
              | Con ("Task", _) -> unrun ()
              | _ -> ())
          | _ -> ())
      | _ -> ());
      if resolve c event <> Con (type_key env "vastra.window/Event", []) then
        messages c event handler.span
  | _ -> ()


(* A view's place: a selector, whose view gives html with the file's messages,
   or a window, whose view gives its pixels. *)
let viewed c env (place : Ast.expr) place_ty (draw : Ast.expr) draw_ty =
  let result = fresh c in
  unify c (Fun ([], result, fresh c)) draw_ty;
  match resolve c place_ty with
  | Con ("String", []) ->
      let html = type_key env "vastra.html/Html" in
      if not (Env.mem html env.types) then
        Diagnostic.fail
          (Diagnostic.make ~why:"views" Type place.span "a view in a page gives html"
          |> Diagnostic.note "require vastra.html");
      let m = fresh c in
      unify_at c (Con (html, [ m ])) result draw.span View_html;
      messages c m draw.span
  | Con (w, []) when w = type_key env "vastra.window/Window" ->
      unify_at c (vector (con "U32")) result draw.span View_pixels
  | other ->
      Diagnostic.fail
        (Diagnostic.make ~why:"views" Type place.span
           ("a view's place is a selector, like \"#app\", or a window, not a value of \
             type "
           ^ show_with (namer_of c) (zonk c other)))

(* A name holding a function that acts ends in !, and a function that takes
   functions doesn't share its name, plus !, with another, or a call adding the
   ! could mean either. *)
let named_right c (name : Ast.binding) (value : Ast.expr) ty =
  holds_action c name value ty;
  let takes_functions t =
    let fn p = match resolve c p with Fun _ -> true | _ -> false in
    match resolve c t with Fun (ps, _, _) -> List.exists fn ps | _ -> false
  in
  let n = name.name in
  let plain, other = if bang n then (Ast.unbang n, n) else (n, n ^ "!") in
  let plain_ty =
    if bang n then Option.map (fun (s : scheme) -> s.ty) (Env.find_opt plain c.env.vars)
    else Some ty
  in
  match plain_ty with
  | Some t when takes_functions t && Env.mem (if bang n then plain else other) c.env.vars
    ->
      let plain = shown c.env plain and other = shown c.env other in
      Diagnostic.fail
        (Diagnostic.make ~why:"bang" Type name.name_span
           (Printf.sprintf
              "`%s` takes functions, so `(%s ...)` could call either it or `%s`"
              plain other other)
        |> Diagnostic.note
             "a function that takes functions can't share its name, plus !, with another")
  | _ -> ()

let check ~general ~use ~disputed c (top : Ast.top) =
  let env = c.env in
  c.acts <- fresh c;
  (* A name the file's code set!s holds one type, its open parts fixed by its
     uses, and its maps gain no keys that may be missing. *)
  let changing =
    match top with
    | Def { value = { kind = Fn _; _ }; _ } -> false
    | Def { name; _ } -> Env.mem name.name env.changing
    | _ -> false
  in
  let ty =
    match top with
    | Expr e -> infer c e
    | Def { name; value; _ } when changing -> (
        let ty = close c (infer c value) in
        (* It keeps the unknowns its uses fixed, except one a file [disputed],
           which it leaves behind. *)
        let left = function Unknown (u, _) when List.mem u disputed -> fresh c | t -> t in
        match Env.find_opt name.name env.vars with
        | Some { ty = old; vars = [||]; _ } -> share c ty (knowns c (map_type left old))
        | _ -> ty)
    | Def { name; value = { kind = Fn _; _ } as value; _ } ->
        (* A function may call itself; within its body its name is monomorphic. *)
        let self = mono (fresh c) in
        c.self <- Some self;
        c.naming <- Some name.name;
        let ty = with_locals c [ (name.name, self) ] (fun () -> infer c value) in
        unify_at c self.ty ty name.name_span (Recursion name.name);
        ty
    | Def { value; _ } -> infer c value
    | On { handler; _ } -> infer c handler
    | View { place; draw; _ } ->
        let place_ty = infer c place in
        let draw_ty = infer c draw in
        viewed c env place place_ty draw draw_ty;
        draw_ty
    | Type _ | Native _ | Macro _ | Ns _ -> unit
  in
  (match top with
  | Def { name; value; _ } -> written c name.name name.written ty value.span
  | _ -> ());
  (* A native no written type told gives what it does otherwise. *)
  List.iter
    (fun (d, otherwise, (e : Ast.expr)) ->
      let f = match e.kind with Var f -> f | _ -> "" in
      unify_at c otherwise d e.span (Untold f))
    c.telling;
  (match top with On { handler; waits; _ } -> handles c env handler ~waits ty | _ -> ());
  settle c;
  (match top with Def { name; value; _ } -> named_right c name value ty | _ -> ());
  c.level <- 0;
  as_vectors c ty;
  let reads =
    match top with
    | Expr e | Def { value = e; _ } ->
        let self =
          match top with
          | Def { name; value = { kind = Fn _; _ }; _ } -> Some name.name
          | _ -> None
        in
        Once.check ?self (found c) e
    | _ -> []
  in
  (* A buffer lives only while code runs. *)
  (match top with
  | Def { name; _ } when held c ty = Surely ->
      Diagnostic.fail
        (Diagnostic.make ~why:"buffer-held" Type name.name_span
           "a definition cannot hold a buffer: a buffer lives only while code runs"
        |> Diagnostic.note "buffer/freeze gives it as a vector")
  | _ -> ());
  (match top with
  | Def { value = { kind = Fn _; _ } as fn; _ } | Expr ({ kind = Fn _; _ } as fn) ->
      generic c fn ty
  | _ when general -> ()
  (* ...and at the top level nothing comes after to fix it: it is an Int. *)
  | _ -> List.iter (fun v -> unify c (Var v) int) (told_vars c ty));
  (* So is a literal that meets a name's unknown, in a function too: no later
     use can change the code checked now. *)
  if not general then
    for v = 0 to Dynarray.length c.table - 1 do
      match Dynarray.get c.table v with
      | Unbound (0, k) when told k -> unify c (Var v) int
      (* A child of html is an element. *)
      | Unbound (0, Some (Child h)) -> unify c (Var v) h
      | _ -> ()
    done;
  List.iter (fun note -> note ()) c.later;
  (match top with Def { name; _ } when changing -> wait c name.name ty | _ -> ());
  if not general then
    Hashtbl.iter
      (fun v (u, owner) ->
        match (Ints.find u env.unknowns, Dynarray.get c.table v) with
        | Open _, Link t ->
            let t = kept c owner t in
            c.unknowns <- Ints.add u (Fixed (t, use)) c.unknowns
        | Open _, Unbound (_, k) -> c.unknowns <- Ints.add u (Open k) c.unknowns
        | Fixed _, _ -> ())
      c.named;
  let env = { env with unknowns = c.unknowns; messages = c.messages } in
  match (top, generalize c (zonk ~lazily:true c ty)) with
  (* One cell holds values of one type, like ML's ref. *)
  | Def { name; _ }, scheme when changing && Array.length scheme.vars > 0 ->
      Diagnostic.fail
        (Diagnostic.make ~why:"changing-type" Type name.name_span
           (Printf.sprintf "the type of `%s` is not fully known: %s"
              (shown c.env name.name)
              (Types.show_scheme ~plain:true ~shown:(shown c.env) scheme))
        |> Diagnostic.note
             "set! changes it, so it holds one type: give it a starting value fixing it")
  | _, scheme -> ({ scheme with reads }, env)

(* [general]: an expression's most general type, as :type shows it without
   running it. [use]: how an error names this check, if it fixes a name's
   unknown, and [disputed], the unknowns a file fixes otherwise. [line]:
   the line of a byte of the source, for Once. Also gives the environment with
   what it fixed. *)
let rec check_expr ?(general = false) ?(disputed = []) ?opened ~use ~line env top =
  let c = { (checker env) with opened; line } in
  try check ~general ~use ~disputed c top
  with Diagnostic.Error d when opened = None -> (
    (* An error that a fixed unknown taken as open would not make disagrees
       with the use that fixed it. *)
    let fixed =
      Hashtbl.fold
        (fun _ (u, owner) found ->
          match Ints.find u env.unknowns with
          | Fixed (_, by) -> (u, owner, by) :: found
          | Open _ -> found)
        c.named []
    in
    let over (u, _, _) =
      match check_expr ~general ~disputed ~opened:u ~use ~line env top with
      | _ -> true
      | exception Diagnostic.Error _ -> false
    in
    match List.find_opt over (List.sort compare fixed) with
    | None -> raise (Diagnostic.Error d)
    | Some (u, owner, by) ->
        let name = shown env owner in
        Diagnostic.fail
          { (Diagnostic.note
             (match Env.find_opt owner env.vars with
             | Some s when Env.mem owner env.changing ->
                 Printf.sprintf "`%s` holds %s, fixed %s" name
                   (show_scheme ~plain:true ~shown:(shown env)
                      { s with ty = resolved env s.ty })
                   by
             | _ -> Printf.sprintf "the type of `%s` was fixed %s" name by)
             d) with against = Some (owner, u) })

(* The same type, as a redefinition keeps it. *)
let same env a b =
  let r (s : scheme) = { s with ty = resolved env s.ty } in
  Types.same (r a) (r b)

(* A macro is a function from forms to a Form, or to a (Result String Form)
   when it may reject its input. The rest parameter collects the extra forms. *)
let check_macro env (params : Ast.binding list) (rest : Ast.binding option)
    (body : Ast.expr) =
  let c = { (checker env) with place = Macro_body } in
  c.acts <- fresh c;
  let form = con "Form" in
  let bindings =
    List.map (fun (p : Ast.binding) -> (p.name, mono form)) params
    @ Option.to_list
        (Option.map
           (fun (r : Ast.binding) -> (r.name, mono (vector form)))
           rest)
  in
  let result = with_locals c bindings (fun () -> infer c body) in
  settle c;
  (try unify c form result
   with Unify _ -> (
     try unify c (Con ("Result", [ str; form ])) result
     with Unify _ ->
       Diagnostic.fail
         (Diagnostic.make ~why:"quasiquote" Type body.span
            ("a macro must return a Form or a (Result String Form), not "
            ^ show_with (namer_of c) (zonk c result)))));
  List.iter (fun note -> note ()) c.later
