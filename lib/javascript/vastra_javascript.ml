(* What vastra build --js writes: a checked program as plain JavaScript. An Int
   is a number while it is a safe integer and a BigInt past that, a Float a
   number, a map an object, a vector an array, a buffer of Floats a
   Float64Array, a constructor {tag, 0: …}. A task is a generator: a function
   that gives one is a generator function, and a task value one of no
   arguments; the runtime runs them as vastra run does.
   Natives come from runtime.js, only those the program uses. *)

open Vastra
open Ast

exception Unsupported of string
exception Refused of string

let p = Printf.sprintf
let fail what = raise (Unsupported what)
let unversioned n = List.hd (String.split_on_char ' ' n)

(* Compact output is the default; --readable writes it for a reader. *)
let compact = ref true

let reserved =
  [ "new"; "delete"; "default"; "class"; "function"; "var"; "let"; "const"; "in"; "do";
    "for"; "if"; "else"; "return"; "this"; "switch"; "case"; "typeof"; "void"; "with";
    "yield"; "await"; "import"; "export"; "super"; "null"; "true"; "false"; "try";
    "catch"; "finally"; "throw"; "while"; "break"; "continue"; "enum"; "static" ]

(* string/fixed → stringFixed, empty? → isEmpty, count-by! → countBy, @1 → _1. *)
let camel name =
  let ends c = String.ends_with ~suffix:c name in
  let question = ends "?" in
  let name = if question || ends "!" then String.sub name 0 (String.length name - 1) else name in
  let words = String.split_on_char '-' (String.map (function '/' | '.' -> '-' | c -> c) name) in
  let words = (if question then [ "is" ] else []) @ List.filter (( <> ) "") words in
  let s = String.concat "" (List.mapi (fun i w -> if i = 0 then w else String.capitalize_ascii w) words) in
  let s = String.map (fun c -> match c with 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' -> c | _ -> '_') s in
  let s = if s = "" then "_" else s in
  if List.mem s reserved then s ^ "_" else s

let js_string s =
  let b = Buffer.create (String.length s + 2) in
  Buffer.add_char b '"';
  String.iter
    (function
      | '"' -> Buffer.add_string b "\\\""
      | '\\' -> Buffer.add_string b "\\\\"
      | '\n' -> Buffer.add_string b "\\n"
      | c when Char.code c < 0x20 -> Buffer.add_string b (p "\\u%04x" (Char.code c))
      | c -> Buffer.add_char b c)
    s;
  Buffer.add_char b '"';
  Buffer.contents b

let js_float f =
  if Float.is_nan f then "NaN"
  else if Float.is_integer f && Float.abs f < 1e15 then p "%.1f" f
  else if Float.abs f = Float.infinity then if f > 0. then "Infinity" else "-Infinity"
  else
    let plain = List.init 21 (fun k -> p "%.*f" k f) in
    let reads s = float_of_string s = f in
    match List.find_opt reads plain with
    | Some s when Float.abs f >= 1e-6 && Float.abs f < 1e21 -> s
    | _ -> List.find reads [ p "%.15g" f; p "%.16g" f; p "%.17g" f ]

let number s =
  if not !compact then s
  else
    let s = if String.ends_with ~suffix:".0" s then String.sub s 0 (String.length s - 2) else s in
    if String.starts_with ~prefix:"0." s then String.sub s 1 (String.length s - 1) else s

let identifier k =
  k <> "" && String.for_all (function 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' -> true | _ -> false) k
  && not (match k.[0] with '0' .. '9' -> true | _ -> false)

let key k = if identifier k then k else js_string k

(* A name as an object's property, where JavaScript's words are allowed: html/class → class. *)
let property name =
  let c = camel name in
  let n = String.length c in
  if n > 1 && c.[n - 1] = '_' && List.mem (String.sub c 0 (n - 1)) reserved then String.sub c 0 (n - 1) else c
let member k = if identifier k then "." ^ k else "[" ^ js_string k ^ "]"

(* JavaScript's precedences, as far as this printer needs them. *)
let atom = 20 and call = 18 and unary = 14 and mul = 12 and add = 11 and shift = 10 and rel = 9
and eq = 8 and bitand = 7 and bitxor = 6 and bitor = 5 and and_ = 4 and or_ = 3 and ternary = 2
and arrow = 1

let paren level (s, prec) = if prec < level then "(" ^ s ^ ")" else s

(* c ? a : b, on three lines when it is long. *)
let conditional c a b =
  let line = p "%s ? %s : %s" c a b in
  if String.length line <= 76 && not (String.contains line '\n') then line
  else p "%s\n  ? %s\n  : %s" c (String.concat "\n  " (String.split_on_char '\n' a)) (String.concat "\n  " (String.split_on_char '\n' b))

(* Items on one line if they fit, else one a line. *)
let layout ?(trailing = true) opening items closing =
  let line = opening ^ String.concat ", " items ^ closing in
  if String.length line <= 76 && not (String.contains line '\n') then line
  else
    let rec init = function [ _ ] | [] -> [] | x :: rest -> x :: init rest in
    let last = match List.rev items with l :: _ -> l | [] -> "" in
    let short = String.concat ", " (init items) in
    if closing = ")" && String.length short <= 40 && not (String.contains short '\n')
       && last <> "" && String.contains "[{(a" last.[0] && String.contains last '\n'
    then opening ^ (if short = "" then "" else short ^ ", ") ^ last ^ closing
    else
      let n = List.length items in
      let item i l = String.concat "\n" (List.map (fun l -> "  " ^ l) (String.split_on_char '\n' (if trailing || i < n - 1 then l ^ "," else l))) in
      opening ^ "\n" ^ String.concat "\n" (List.mapi item items) ^ "\n" ^ closing
let indent lines =
  List.concat_map (fun l -> List.map (fun l -> if l = "" then l else "  " ^ l) (String.split_on_char '\n' l)) lines
let block lines = String.concat "\n" (indent lines)

(* Whether a type, as the checker writes it, is a task, or a function giving one. *)
let rec is_task (n : Reader.node) =
  match n.form with List ({ form = Symbol "Task"; _ } :: _) -> true | _ -> false

and gives_task (n : Reader.node) =
  match n.form with
  | List ({ form = Symbol ("->" | "->?"); _ } :: rest) -> (
      match List.rev rest with last :: _ -> is_task last | [] -> false)
  | _ -> false

let read_type ty = match Reader.read_all ty with Ok [ n ] -> Some n | _ -> None

(* What a number may be, as far as the printer can tell: between lo and hi, or
   NaN where nan says so. An Int is never NaN. *)
type range = { lo : float; hi : float; nan : bool }

let any = { lo = Float.neg_infinity; hi = Float.infinity; nan = true }
let exact x = if Float.is_nan x then any else { lo = x; hi = x; nan = false }
let within lo hi = { lo; hi; nan = false }
let union a b = { lo = Float.min a.lo b.lo; hi = Float.max a.hi b.hi; nan = a.nan || b.nan }
let widened old r =
  { r with lo = (if r.lo < old.lo then Float.neg_infinity else r.lo); hi = (if r.hi > old.hi then Float.infinity else r.hi) }

(* Every value is a safe integer: an Int that is a JavaScript number. *)
let safe r = (not r.nan) && r.lo >= -9007199254740991. && r.hi <= 9007199254740991.
let int32 r = r.lo > -2147483648. && r.hi < 2147483648.

(* Interval arithmetic. Where infinities meet, or one meets 0, NaN may come. *)
let bounds nan xs =
  if List.exists Float.is_nan xs then any
  else { lo = List.fold_left Float.min Float.infinity xs; hi = List.fold_left Float.max Float.neg_infinity xs; nan }
let negate r = { r with lo = -.r.hi; hi = -.r.lo }
let plus a b = bounds (a.nan || b.nan) [ a.lo +. b.lo; a.hi +. b.hi ]
let minus a b = plus a (negate b)
let times a b = bounds (a.nan || b.nan) [ a.lo *. b.lo; a.lo *. b.hi; a.hi *. b.lo; a.hi *. b.hi ]
let divide a b =
  if b.lo <= 0. && b.hi >= 0. then any else bounds (a.nan || b.nan) [ a.lo /. b.lo; a.lo /. b.hi; a.hi /. b.lo; a.hi /. b.hi ]

(* a and b where a < b holds (a <= b, unless strict). Found from a comparison
   that was false, NaN may be why: then nan stays, and a NaN side says nothing
   of the other. *)
let order ~strict ~int ~sure a b =
  let step = if strict && int then 1. else 0. in
  let a' = if b.nan && not sure then a else { a with hi = Float.min a.hi (b.hi -. step); nan = a.nan && not sure } in
  let b' = if a.nan && not sure then b else { b with lo = Float.max b.lo (a.lo +. step); nan = b.nan && not sure } in
  (a', b')

let meet a b = { lo = Float.max a.lo b.lo; hi = Float.min a.hi b.hi; nan = a.nan && b.nan }

(* x * x, which is never below 0. *)
let square a = let r = times a a in if a.lo < 0. && a.hi > 0. then { r with lo = 0. } else r

let rec has_var = function
  | Types.Var _ -> true
  | Con (_, ts) -> List.exists has_var ts
  | Fun (ps, r, _) -> List.exists has_var (r :: ps)
  | Record r -> has_var r
  | Row_extend (_, t, rest) -> has_var t || has_var rest
  | _ -> false

(* What the variables of [pattern] are in [given]; a row's tail is the keys left.
   A type with variables of its own counts only where [vars] allows it. *)
let rec bind_types ?(vars = false) acc (pattern : Types.t) (given : Types.t) =
  let bind_types = bind_types ~vars in
  match (pattern, given) with
  | Var v, t -> if List.mem_assoc v acc || (has_var t && not vars) then acc else (v, t) :: acc
  | Con (a, ps), Con (b, gs) when a = b && List.length ps = List.length gs -> List.fold_left2 bind_types acc ps gs
  | Fun (ps, r, _), Fun (gs, g, _) when List.length ps = List.length gs -> bind_types (List.fold_left2 bind_types acc ps gs) r g
  | Record r, Record g -> bind_types acc r g
  | Row_extend _, _ ->
      let rec split = function Types.Row_extend (k, t, rest) -> let fs, tail = split rest in ((k, t) :: fs, tail) | t -> ([], t) in
      let pf, ptail = split pattern and gf, gtail = split given in
      let acc = List.fold_left (fun acc (k, t) -> match List.assoc_opt k gf with Some g -> bind_types acc t g | None -> acc) acc pf in
      let left = List.fold_right (fun (k, t) rest -> if List.mem_assoc k pf then rest else Types.Row_extend (k, t, rest)) gf gtail in
      bind_types acc ptail left
  | _ -> acc

(* The type of [name] where [e] first uses it. *)
let rec find_var name (e : expr) =
  match e.kind with
  | Var n when n = name -> (match e.typed with Type t -> Some t | _ -> None)
  | _ -> List.find_map (find_var name) (Ast.children e)

(* A value of type [t] may be a buffer, or hold one. *)
let rec maybe_buffer (t : Types.t) =
  match t with
  | Var _ | Con ("Vector", [ _; (Con ("unique", []) | Var _) ]) -> true
  | Record row -> List.exists (fun (_, t) -> maybe_buffer t) (Types.fields row)
  | _ -> false

let is_buffer t = match t with Some (Types.Con ("Vector", [ _; Types.Con ("unique", []) ])) -> true | _ -> false
let fixed_type t = match t with Some (Types.Con (c, [])) when Num.is_name c -> (match Num.of_name c with Num.Fixed f -> Some f | _ -> None) | _ -> None
let typed_array t =
  match t with
  | Some (Types.Con ("Float", [])) -> Some "Float64Array"
  | t -> (
      match fixed_type t with
      | Some Num.U32 -> Some "Uint32Array" | Some Num.I32 -> Some "Int32Array"
      | Some Num.U16 -> Some "Uint16Array" | Some Num.I16 -> Some "Int16Array"
      | Some Num.U8 -> Some "Uint8Array" | Some Num.I8 -> Some "Int8Array"
      | None -> None)
let element t = match t with Some (Types.Con ("Vector", [ a; _ ])) -> Some a | _ -> None

(* A map holding a buffer is held by one name too: it changes in place. *)
let holds_buffer t =
  match t with Some (Types.Record row) -> List.exists (fun (_, t) -> is_buffer (Some t)) (Types.fields row) | _ -> false

let rec names (p : pattern) = match p.pat with PVar n -> [ n ] | PCtor (_, ps) | PVector ps -> List.concat_map names ps | _ -> []

(* Whether [e] is one JavaScript expression, with no statements inside. *)
let rec simple (e : expr) =
  match e.kind with
  | Let _ | Par_let _ | Match _ -> false
  | If { condition; then_branch; else_branch } -> simple condition && simple then_branch && simple else_branch
  | Call { func; args } -> simple func && List.for_all simple args
  | Vector xs -> List.for_all simple xs
  | Record fs -> List.for_all (fun (_, v) -> simple v) fs
  | Get { record; _ } -> simple record
  | Set { target; value; _ } -> simple target && simple value
  | Task_of x -> simple x
  | _ -> true

(* [e] with [f] applied to the expressions directly inside it, in the order they
   run, as a new node. *)
let map_children f (e : expr) =
  let step = function At x -> At (f x) | k -> k in
  let kind =
    match e.kind with
    | Vector xs -> Vector (List.map f xs)
    | Record fs -> Record (List.map (fun (k, v) -> (k, f v)) fs)
    | Get g -> Get { g with record = f g.record }
    | Read { target; path } -> let target = f target in Read { target; path = List.map step path }
    | Set { target; path; value } ->
        let target = f target in
        let path = List.map step path in
        Set { target; path; value = f value }
    | Fn l -> Fn { l with body = f l.body }
    | Let { bindings; body; how } ->
        let bindings = List.map (fun (b, v) -> (b, f v)) bindings in
        Let { bindings; body = f body; how }
    | If { condition; then_branch; else_branch } ->
        let condition = f condition in
        let then_branch = f then_branch in
        If { condition; then_branch; else_branch = f else_branch }
    | Match { scrutinee; clauses } ->
        let scrutinee = f scrutinee in
        Match { scrutinee; clauses = List.map (fun (q, b) -> (q, f b)) clauses }
    | Call { func; args } -> let func = f func in Call { func; args = List.map f args }
    | k -> k
  in
  { e with kind }

(* The ways out of [e], other than calls to [self]. *)
let rec exits self (e : expr) =
  match e.kind with
  | Call { func = { kind = Var n; _ }; _ } when n = self -> []
  | If { then_branch; else_branch; _ } -> exits self then_branch @ exits self else_branch
  | Let { body; _ } | Par_let { body; _ } -> exits self body
  | Match { clauses; _ } -> List.concat_map (fun (_, b) -> exits self b) clauses
  | _ -> [ e ]

(* The keys of the record each of [ways] out gives, if every one gives one. *)
let record_keys ways =
  let keys (e : expr) = match e.kind with Record fs -> Some (List.sort compare (List.map fst fs)) | _ -> None in
  match List.map keys ways with Some ks :: rest when List.for_all (( = ) (Some ks)) rest -> Some ks | _ -> None

let rec size (e : expr) = List.fold_left (fun n c -> n + size c) 1 (Ast.children e)
let rec mentions x (e : expr) = (match e.kind with Var n -> n = x | _ -> false) || List.exists (mentions x) (Ast.children e)

(* What can be written out where it is called: no tasks, no changes of names. *)
let rec plain (e : expr) =
  (match e.kind with
  | Quote _ | Quasi _ | Await _ | Task_of _ | Run _ | Update _ | Change _ | Send _ | Par_let _ -> false
  | _ -> true)
  && List.for_all plain (Ast.children e)

(* The names [e] uses and does not bind itself. *)
let rec free (e : expr) =
  let without ns = List.filter (fun n -> not (List.mem n ns)) in
  match e.kind with
  | Var n -> [ n ]
  | Let { bindings; body; how } ->
      let bound = List.map (fun ((b : binding), _) -> b.name) bindings in
      if how = Recursive then without bound (List.concat_map (fun (_, v) -> free v) bindings @ free body)
      else List.fold_right (fun ((b : binding), v) rest -> free v @ without [ b.name ] rest) bindings (free body)
  | Fn l -> without (List.map (fun (b : binding) -> b.name) l.params) (free l.body)
  | Match { scrutinee; clauses } -> free scrutinee @ List.concat_map (fun (q, b) -> without (names q) (free b)) clauses
  | _ -> List.concat_map free (Ast.children e)

(* The calls to each name, and the names used other than called. *)
let uses entries =
  let calls = Hashtbl.create 64 and as_value = Hashtbl.create 64 in
  let rec count (e : expr) =
    match e.kind with
    | Call { func = { kind = Var n; _ }; args } ->
        Hashtbl.replace calls n (1 + Option.value (Hashtbl.find_opt calls n) ~default:0);
        List.iter count args
    | Var n -> Hashtbl.replace as_value n ()
    | _ -> List.iter count (Ast.children e)
  in
  List.iter
    (fun (top, _, _) ->
      match top with
      | Def { value = e; _ } | Expr e | On { handler = e; _ } -> count e
      | View { place; draw; _ } -> count place; count draw
      | _ -> ())
    entries;
  (calls, as_value)

(* Names the printer makes start with #, as no name of a program can: #x~3 is
   written x. *)
let base_name n = Str.global_replace (Str.regexp "#\\|~[0-9]+") "" n
let made = ref 0
let made_name base = incr made; p "#%s~%d" (base_name base) !made
let binding_of (e : expr) name : binding = { name; name_span = e.span; written = None }
let let_ bs (body : expr) =
  List.fold_right (fun b (body : expr) -> { body with kind = Let { bindings = [ b ]; body; how = Names } }) bs body

(* [t] with a type's parameters, [Gen i], replaced by [args]. *)
let rec given args (t : Types.t) : Types.t =
  match t with
  | Gen i -> List.nth args i
  | Con (c, ts) -> Con (c, List.map (given args) ts)
  | Fun (ps, r, a) -> Fun (List.map (given args) ps, given args r, given args a)
  | Record r -> Record (given args r)
  | Row_extend (k, t, r) -> Row_extend (k, given args t, given args r)
  | t -> t

(* The functions [e] calls as its last step, whose value is its own: in each
   branch, a let's body, a clause. *)
let rec last_calls (e : expr) =
  match e.kind with
  | Call { func; _ } -> [ func ]
  | If { then_branch; else_branch; _ } -> last_calls then_branch @ last_calls else_branch
  | Let { body; _ } -> last_calls body
  | Match { clauses; _ } -> List.concat_map (fun (_, b) -> last_calls b) clauses
  | _ -> []

(* A branch that never names a buffer another branch names lets it go as it
   starts, and the runtime keeps it for the next copy of its kind and length.
   One name holds a buffer, and nothing after the branch can name this
   one, so nothing else holds it. [held]: the buffers [typed] keeps, with their
   types, named by a let whose scope ends where [e] does. A parameter is never
   one: its caller may only lend it. *)
let rec let_go typed held (e : expr) =
  let go = let_go typed and outside ns = List.filter (fun (n, _) -> not (List.mem n ns)) in
  (* Each branch, from the names it binds, with what it lets go first. *)
  let branches bs =
    let named = List.map (fun (q, b) -> List.filter (fun n -> not (List.mem n q)) (free b)) bs in
    List.map2
      (fun (q, (b : expr)) mine ->
        let held = outside q held in
        let gone = List.filter (fun (n, _) -> (not (List.mem n mine)) && List.exists (List.mem n) named) held in
        let spare (n, t) (body : expr) =
          let x = { body with kind = Var n; typed = Type t } in
          let_ [ (binding_of body "_", { body with kind = Call { func = { body with kind = Var "#spare" }; args = [ x ] } }) ] body
        in
        List.fold_right spare gone (go held b))
      bs named
  in
  match e.kind with
  | Let { bindings; body; how } ->
      let bound = List.map (fun ((b : binding), _) -> b.name) bindings in
      let mine = List.filter_map (fun n -> match find_var n body with Some t when typed t -> Some (n, t) | _ -> None) bound in
      let bindings = List.map (fun (b, v) -> (b, go [] v)) bindings in
      { e with kind = Let { bindings; body = go (mine @ outside bound held) body; how } }
  | If { condition; then_branch; else_branch } -> (
      match branches [ ([], then_branch); ([], else_branch) ] with
      | [ then_branch; else_branch ] -> { e with kind = If { condition = go [] condition; then_branch; else_branch } }
      | _ -> assert false)
  | Match { scrutinee; clauses } ->
      let bodies = branches (List.map (fun (q, b) -> (names q, b)) clauses) in
      { e with kind = Match { scrutinee = go [] scrutinee; clauses = List.map2 (fun (q, _) b -> (q, b)) clauses bodies } }
  | _ -> map_children (go []) e

(* [e] as a new copy, with new names for what it binds and its types through
   [ty]; [env] gives each name's replacement. *)
let rec renamed ty env (e : expr) =
  let fresh env (b : binding) =
    let n = made_name b.name in
    ((b.name, fun (v : expr) -> { v with kind = Var n; typed = ty v.typed }) :: env, { b with name = n })
  in
  let rec pattern env (q : pattern) =
    match q.pat with
    | PVar n ->
        let n' = made_name n in
        ((n, fun (v : expr) -> { v with kind = Var n'; typed = ty v.typed }) :: env, { q with pat = PVar n' })
    | PCtor (c, ps) -> let env, ps = patterns env ps in (env, { q with pat = PCtor (c, ps) })
    | PVector ps -> let env, ps = patterns env ps in (env, { q with pat = PVector ps })
    | _ -> (env, q)
  and patterns env ps = List.fold_left (fun (env, acc) q -> let env, q = pattern env q in (env, acc @ [ q ])) (env, []) ps in
  let go = renamed ty in
  let binders env bs = List.fold_left (fun (env, acc) b -> let env, b = fresh env b in (env, acc @ [ b ])) (env, []) bs in
  match e.kind with
  | Var n -> (match List.assoc_opt n env with Some f -> f e | None -> { e with kind = e.kind; typed = ty e.typed })
  | _ ->
      let copy =
        match e.kind with
        | Let { bindings; body; how = Recursive } ->
            let env, bs = binders env (List.map fst bindings) in
            let bindings = List.map2 (fun b (_, v) -> (b, go env v)) bs bindings in
            { e with kind = Let { bindings; body = go env body; how = Recursive } }
        | Let { bindings; body; how } ->
            let env, bindings =
              List.fold_left
                (fun (env, bs) (b, v) -> let v = go env v in let env, b = fresh env b in (env, bs @ [ (b, v) ]))
                (env, []) bindings
            in
            { e with kind = Let { bindings; body = go env body; how } }
        | Fn l ->
            let env, params = binders env l.params in
            { e with kind = Fn { params; body = go env l.body } }
        | Match { scrutinee; clauses } ->
            let scrutinee = go env scrutinee in
            let clause (q, b) = let env, q = pattern env q in (q, go env b) in
            { e with kind = Match { scrutinee; clauses = List.map clause clauses } }
        | _ -> map_children (go env) e
      in
      copy.typed <- ty e.typed;
      copy

(* The types a call of a function with [typed] and [l] gives its variables: a
   number variable the type its use [f] names, the others from the arguments. *)
let types_of (f : expr) (typed : typed) (l : lambda) (args : expr list) =
  let numbers =
    match (f.typed, typed) with
    | Use ns, Generic vars when List.length ns = List.length vars ->
        List.combine vars (List.map (function Known t -> Types.con (Num.name t) | Hidden w -> Types.Var w) ns)
    | _ -> []
  in
  let params =
    match typed with
    | Type (Fun (ps, _, _)) -> List.map Option.some ps
    | _ -> List.map (fun (b : binding) -> find_var b.name l.body) l.params
  in
  let given (a : expr) =
    match a.typed with Type t -> Some t | Literal (Known n) | Use [ Known n ] -> Some (Types.con (Num.name n)) | _ -> None
  in
  let others =
    let bind acc p a = match (p, given a) with Some p, Some t -> bind_types ~vars:true acc p t | _ -> acc in
    if List.length params <> List.length args then [] else List.fold_left2 bind [] params args
  in
  numbers @ List.filter (fun (v, _) -> not (List.mem_assoc v numbers)) others

(* [typed] with the types [subst] gives variables. *)
let retyped subst (typed : typed) =
  let num = function
    | Hidden v as n -> (
        match List.assoc_opt v subst with
        | Some (Types.Con (c, [])) when Num.is_name c -> Known (Num.of_name c)
        | Some (Types.Var w) -> Hidden w
        | _ -> n)
    | n -> n
  in
  let var = function Types.Var v as t -> Option.value (List.assoc_opt v subst) ~default:t | t -> t in
  match typed with
  | Type t -> (Type (Infer.map_type var t) : typed)
  | Literal n -> Literal (num n)
  | Use ns -> Use (List.map num ns)
  | t -> t

(* A function a let names, generic over numbers but used at one set of number
   types, is one function at those types: its literals and arithmetic know them. *)
let rec local_types (e : expr) =
  let e = map_children local_types e in
  let rec uses n (e : expr) =
    (match (e.kind, e.typed) with Var m, Use ns when m = n -> [ ns ] | _ -> []) @ List.concat_map (uses n) (Ast.children e)
  in
  match e.kind with
  | Let ({ bindings = [ (b, ({ kind = Fn _; typed = Generic vars; _ } as fn)) ]; body; _ } as l) -> (
      match List.sort_uniq compare (uses b.name body) with
      | [ ns ] when List.length ns = List.length vars ->
          let types = List.map (function Known t -> Types.con (Num.name t) | Hidden w -> Types.Var w) ns in
          let fn = renamed (retyped (List.combine vars types)) [] fn in
          { e with kind = Let { l with bindings = [ (b, { fn with typed = Untyped }) ] } }
      | _ -> e)
  | _ -> e

(* A call to one of [small]'s functions is its body, written out there: an
   argument that is not a name or a literal is named first, in order. Each call's
   numbers then have ranges of their own, and a map it gives back can be its
   fields. [scope]: the local names where the call is; a body that means
   something else by one of them stays a call. *)
let rec inline small stack scope (e : expr) =
  let go = inline small stack in
  match e.kind with
  | Call { func = { kind = Var f; _ } as func; args } -> (
      let args = List.map (go scope) args in
      match Hashtbl.find_opt small f with
      | Some (typed, (l : lambda))
        when (not (List.mem f scope || List.mem f stack))
             && List.length l.params = List.length args
             && List.for_all
                  (fun n -> (not (List.mem n scope)) || List.exists (fun (b : binding) -> b.name = n) l.params)
                  (free l.body)
             (* a function generic over numbers needs the types of this use *)
             && (match (typed, func.typed) with
                | Generic vars, Use ns -> List.length vars = List.length ns
                | Generic _, _ -> false
                | _ -> true) ->
          let env, bs =
            List.fold_left2
              (fun (env, bs) (b : binding) (a : expr) ->
                match a.kind with
                | Var _ | Int _ | Hex _ | Float _ | Bool _ | Str _ ->
                    ((b.name, fun (_ : expr) -> { a with kind = a.kind }) :: env, bs)
                | _ ->
                    let n = made_name b.name in
                    let named (v : expr) = { v with kind = Var n; typed = a.typed } in
                    ((b.name, named) :: env, bs @ [ (binding_of a n, a) ]))
              ([], []) l.params args
          in
          let scope = List.map (fun ((b : binding), _) -> b.name) bs @ scope in
          let_ bs (inline small (f :: stack) scope (renamed (retyped (types_of func typed l args)) env l.body))
      | _ -> { e with kind = Call { func; args } })
  | Let { bindings; body; how } ->
      let scope, bindings =
        List.fold_left
          (fun (scope, bs) ((b : binding), v) ->
            let inner = b.name :: scope in
            (inner, bs @ [ (b, go (if how = Recursive then inner else scope) v) ]))
          (scope, []) bindings
      in
      { e with kind = Let { bindings; body = go scope body; how } }
  | Fn l -> { e with kind = Fn { l with body = go (List.map (fun (b : binding) -> b.name) l.params @ scope) l.body } }
  | Match { scrutinee; clauses } ->
      let scrutinee = go scope scrutinee in
      { e with kind = Match { scrutinee; clauses = List.map (fun (q, b) -> (q, go (names q @ scope) b)) clauses } }
  | Par_let _ | Quasi _ | Task_of _ | Await _ | Run _ | Update _ | Change _ | Send _ -> e
  | _ -> map_children (go scope) e

(* Lets moved out of expressions to where statements go, so they print as
   statements: what a value names goes before it, and a branching value that
   then holds statements is named itself. A let never moves past code that
   [touches] a buffer if it touches one too. *)
let floated ~touches =
  let one (e : expr) =
    match e.kind with
    | Match { scrutinee = { kind = Var _; _ }; clauses } -> List.for_all (fun (_, b) -> simple b) clauses
    | _ -> simple e
  in
  let rec stmt (e : expr) =
    match e.kind with
    | Let { bindings; body; how = Names | Changes } -> let_ (List.concat_map value bindings) (stmt body)
    | If _ | Match _ -> let bs, e = branching e in let_ bs e
    | _ -> let bs, e = lift e in let_ bs e
  and value (b, (v : expr)) =
    match v.kind with
    | Let { bindings; body; how = Names | Changes } -> List.concat_map value bindings @ value (b, body)
    | If _ | Match _ -> let bs, v = branching v in bs @ [ (b, v) ]
    | _ -> let bs, v = lift v in bs @ [ (b, v) ]
  and branching (e : expr) =
    match e.kind with
    | If { condition; then_branch; else_branch } ->
        let bs, condition = lift condition in
        (bs, { e with kind = If { condition; then_branch = stmt then_branch; else_branch = stmt else_branch } })
    | Match { scrutinee; clauses } ->
        let bs, scrutinee = lift scrutinee in
        (bs, { e with kind = Match { scrutinee; clauses = List.map (fun (q, b) -> (q, stmt b)) clauses } })
    | _ -> ([], e)
  and lift (e : expr) =
    match e.kind with
    | Let { bindings; body; how = Names | Changes } ->
        let bs = List.concat_map value bindings in
        let more, e = lift body in
        (bs @ more, e)
    | If _ | Match _ ->
        let bs, e = branching e in
        if one e then (bs, e) else let n = made_name "it" in (bs @ [ (binding_of e n, e) ], { e with kind = Var n })
    | Fn l -> ([], { e with kind = Fn { l with body = stmt l.body } })
    | Call _ | Vector _ | Record _ | Get _ | Read _ | Set _ ->
        let before = ref [] and passed = ref [] in
        let e =
          map_children
            (fun c ->
              let bs, c = lift c in
              let c =
                if List.exists (fun (_, v) -> touches v) bs && List.exists touches !passed then let_ bs c
                else (before := !before @ bs; c)
              in
              passed := c :: !passed;
              c)
            e
        in
        (!before, e)
    | _ -> ([], e)
  in
  stmt

(* Short names in order: a, b, … Z, aa, ab, …, never one of JavaScript's words or [avoid]. *)
let namer avoid =
  let letters = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ" in
  let rec spell i = (if i >= 52 then spell ((i / 52) - 1) else "") ^ String.make 1 letters.[i mod 52] in
  let count = ref 0 in
  let rec next () =
    let s = spell !count in
    incr count;
    if List.mem s reserved || avoid s then next () else s
  in
  next

(* runtime.js's paragraphs that hold code, each named by its first line,
   function x, function* x, const x or let x; "" when it has none of these. *)
let paragraphs () =
  let code chunk = List.filter (fun l -> not (String.starts_with ~prefix:"//" l)) (String.split_on_char '\n' chunk) in
  let name chunk =
    match String.split_on_char ' ' (List.hd (code chunk)) with
    | ("function" | "function*" | "const" | "let") :: n :: _ -> List.hd (String.split_on_char '(' n)
    | _ -> ""
  in
  let chunks = Str.split (Str.regexp "\n\n+") Runtime_source.source in
  List.filter_map (fun c -> if code c = [] then None else Some (name c, c)) chunks

(* runtime.js, a function or a value a paragraph, by its name. *)
let runtime_chunks () = List.filter (fun (n, _) -> n <> "") (paragraphs ())

(* JavaScript without comments, and without the spaces only a reader needs. Only
   for what this printer and runtime.js write: strings in double quotes, and a
   regular expression only where an operator or a keyword comes before it. *)
let word c = match c with 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' | '$' -> true | _ -> false

(* JavaScript's tokens, without comments and spaces. Only for what this printer
   and runtime.js write: strings in double quotes, and a regular expression only
   where an operator or a keyword comes before it. *)
let tokens src =
  let n = String.length src in
  let operators = [ "==="; "!=="; "..."; "=>"; "=="; "!="; "<="; ">="; "&&"; "||"; "++"; "--"; "??"; "?."; "+="; "-=" ] in
  let before_regex = [ ""; "("; ","; "="; ":"; "["; "!"; "&&"; "||"; "?"; "{"; "}"; ";"; "return"; "=>" ] in
  let until j stop = let rec go j = if stop j then j else go (j + 1) in go j in
  let rec scan i last acc =
    if i >= n then List.rev acc
    else
      let c = src.[i] in
      let take j = let t = String.sub src i (j - i) in scan j t (t :: acc) in
      if c = ' ' || c = '\n' || c = '\t' then scan (i + 1) last acc
      else if c = '/' && i + 1 < n && src.[i + 1] = '/' then scan (until i (fun j -> j >= n || src.[j] = '\n')) last acc
      else if c = '"' then
        (* An escape is two characters, so "\\" ends at its second quote. *)
        let rec close j = if src.[j] = '\\' then close (j + 2) else if src.[j] = '"' then j else close (j + 1) in
        take (close (i + 1) + 1)
      else if c = '/' && List.mem last before_regex then
        let j = until (i + 1) (fun j -> src.[j] = '/' && src.[j - 1] <> '\\') in
        take (until (j + 1) (fun j -> j >= n || not (word src.[j])))
      else if word c then take (until i (fun j -> j >= n || not (word src.[j])))
      else
        let op = List.find_opt (fun o -> i + String.length o <= n && String.sub src i (String.length o) = o) operators in
        take (i + String.length (Option.value op ~default:"x"))
  in
  scan 0 "" []

(* Tokens joined with a space only where two would read as one, and no , or ;
   left before a closing bracket. *)
let join toks =
  let out = Buffer.create 1024 in
  let last = ref "" in
  List.iter
    (fun t ->
      let drop c = Buffer.length out > 0 && Buffer.nth out (Buffer.length out - 1) = c in
      if (t = "}" || t = "]" || t = ")") && drop ',' then Buffer.truncate out (Buffer.length out - 1);
      if t = "}" && drop ';' then Buffer.truncate out (Buffer.length out - 1);
      let l = !last in
      let ends = if l = "" then ' ' else l.[String.length l - 1] in
      if (word ends && word t.[0]) || ((ends = '+' || ends = '-') && t.[0] = ends) then Buffer.add_char out ' ';
      Buffer.add_string out t;
      last := t)
    toks;
  Buffer.contents out

let compactify src = join (tokens src)

(* A name of runtime.js's own, not one of JavaScript's words. *)
let js_name s =
  s <> "" && (match s.[0] with 'a' .. 'z' | 'A' .. 'Z' | '_' | '$' -> true | _ -> false)
  && not (List.mem s ("of" :: "async" :: "instanceof" :: "typeof" :: reserved))

(* Whether token [i] of [t] is a property: after ., or a key in { key: value }.
   runtime.js keeps to what makes this safe: no object shorthand or
   destructuring, so a property is never one of its names. *)
let is_property t i =
  (i > 0 && t.(i - 1) = ".") || (i + 1 < Array.length t && t.(i + 1) = ":" && i > 0 && (t.(i - 1) = "{" || t.(i - 1) = ","))

(* The names a runtime paragraph's tokens [t] declare: its functions', their
   parameters' and its variables', apart from the paragraph's own name. *)
let declared t =
  let n = Array.length t in
  let declared = ref [] in
  let own = if n > 1 && (t.(0) = "const" || t.(0) = "let") then t.(1) else "" in
  let declare s = if js_name s && s <> own && not (List.mem s !declared) then declared := !declared @ [ s ] in
  (* The names inside the brackets that open at [i], at their first level, ...rest
     too; it gives where they close. *)
  let inside i =
    let close = match t.(i) with "(" -> ")" | "[" -> "]" | _ -> "}" in
    let rec go j depth = if j < n && not (depth = 0 && t.(j) = close) then (
        if depth = 0 && js_name t.(j) && List.mem t.(j - 1) [ t.(i); ","; "..." ] then declare t.(j);
        go (j + 1) (match t.(j) with "(" | "[" | "{" -> depth + 1 | ")" | "]" | "}" -> depth - 1 | _ -> depth)) else j in
    go (i + 1) 0
  in
  let back_to_open i =
    let rec go j depth = if t.(j) = "(" && depth = 0 then j else go (j - 1) (match t.(j) with ")" -> depth + 1 | "(" -> depth - 1 | _ -> depth) in
    go (i - 1) 0
  in
  for i = 0 to n - 1 do
    match t.(i) with
    | "const" | "let" when i + 1 < n ->
        let after = if t.(i + 1) = "[" then inside (i + 1) + 1 else (declare t.(i + 1); i + 2) in
        (* let a = 1, b: the name after each comma at the first level *)
        let rec more j depth =
          if j < n && not (depth = 0 && (t.(j) = ";" || t.(j) = "of" || t.(j) = ")")) then (
            if depth = 0 && t.(j) = "," && j + 1 < n then declare t.(j + 1);
            more (j + 1) (match t.(j) with "(" | "[" | "{" -> depth + 1 | ")" | "]" | "}" -> depth - 1 | _ -> depth))
        in
        more after 0
    | "function" ->
        (* function* is two tokens. *)
        let j = if i + 1 < n && t.(i + 1) = "*" then i + 1 else i in
        if j + 2 < n && t.(j + 2) = "(" then ignore (inside (j + 2)) else if j + 1 < n && t.(j + 1) = "(" then ignore (inside (j + 1))
    | "=>" when i > 0 -> if t.(i - 1) = ")" then ignore (inside (back_to_open (i - 1))) else declare t.(i - 1)
    | "catch" when i + 2 < n && t.(i + 1) = "(" -> declare t.(i + 2)
    | _ -> ()
  done;
  !declared

(* What a paragraph uses and doesn't declare: other paragraphs' names,
   JavaScript's, and Vastra's constructors'. *)
let undeclared chunk =
  let t = Array.of_list (tokens chunk) in
  let own = declared t in
  List.sort_uniq compare
    (List.filteri (fun i s -> js_name s && (not (is_property t i)) && not (List.mem s own)) (Array.to_list t))

(* A runtime function's own names, shortened. *)
let shorten chunk =
  let t = Array.of_list (tokens chunk) in
  let declared = declared t in
  let free = List.filter (fun s -> js_name s && not (List.mem s declared)) (Array.to_list t) in
  let next = namer (fun s -> List.mem s free || List.mem s [ "of"; "async" ]) in
  let short = List.map (fun s -> (s, next ())) declared in
  let renamed i s = match List.assoc_opt s short with Some r when not (is_property t i) -> r | _ -> s in
  join (List.mapi renamed (Array.to_list t))

let program ~show path source =
  let s = Session.create ~base_dir:(Filename.dirname path) ~trace:true () in
  s.check_only <- true;
  s.run_tasks <- not show;  (* as vastra build: a definition may run a task; --show shows it *)
  s.platform <- "js";
  (match Session.eval_source ~file:path s source with
  | Error d -> raise (Refused (Diagnostic.render d source path))
  | Ok _ -> ());
  let entries = List.rev (Option.value s.trace ~default:[]) in
  let how = Compile.globals entries and needed = Compile.needed entries in
  let used n = Hashtbl.mem needed n in
  let shown n = Infer.shown s.state.env n in
  let tag n = let n = unversioned n in match String.rindex_opt n '/' with Some i -> String.sub n (i + 1) (String.length n - i - 1) | None -> n in
  (* What gives a task: natives by their written type, functions by their checked one. *)
  let tasks = Hashtbl.create 16 in
  List.iter
    (fun (top, outcome, _) ->
      match (top, outcome) with
      | Native { name; ty }, _ when gives_task ty -> Hashtbl.replace tasks name.name ()
      | Def { name; _ }, Session.Defined { ty; _ } -> (
          match read_type ty with
          | Some t when gives_task t -> Hashtbl.replace tasks name.name ()
          | _ -> ())
      | _ -> ())
    entries;
  let gives_task n = Hashtbl.mem tasks n in
  (* The program's own names. Everything else is Vastra's, inside one object, vastra,
     so no name of the program's clashes with one of Vastra's. *)
  let own = Hashtbl.create 32 in
  List.iter
    (fun (top, _, shown) ->
      match top with
      | (Def { name; _ } | Native { name; _ }) when shown -> Hashtbl.replace own name.name ()
      | Type { ctors; _ } when shown -> List.iter (fun (c : Ast.ctor) -> Hashtbl.replace own c.ctor_name ()) ctors
      | Ns { name; imports; _ } when shown -> List.iter (fun (i : Ast.import) -> Hashtbl.replace own (name ^ "/" ^ i.local) ()) imports
      | _ -> ())
    entries;
  let mine = ref false (* printing the program's own code *) and exports = Hashtbl.create 16 in
  (* Compact names never meet a name vastra's own functions use inside it. *)
  let inside = Hashtbl.create 64 in
  List.iter (fun (n, _) -> Hashtbl.replace inside n ()) (runtime_chunks ());
  List.iter
    (fun (top, _, shown) ->
      match top with
      | (Def { name; _ } | Native { name; _ }) when not shown -> Hashtbl.replace inside (camel (unversioned name.name)) ()
      | Type { ctors; _ } -> List.iter (fun (c : Ast.ctor) -> Hashtbl.replace inside (camel (tag c.ctor_name)) ()) ctors
      | _ -> ())
    entries;
  let fresh = namer (Hashtbl.mem inside) and next_key = namer (fun _ -> false) in
  let vastra = if !compact then fresh () else "vastra" in
  let shorts = Hashtbl.create 16 and keys = Hashtbl.create 16 in
  let short table make n = match Hashtbl.find_opt table n with Some s -> s | None -> let s = make () in Hashtbl.add table n s; s in
  let qualified n =
    let n = unversioned n in
    if String.starts_with ~prefix:"vastra." n then String.sub n 7 (String.length n - 7) else n
  in
  (* html/element is htmlElement inside vastra, and vastra.html.element from the program. *)
  let internal n = camel (qualified n) in
  (* A runtime function is always reached through vastra, even when the
     program has a function of the same name. *)
  let reach ?(runtime = false) n js =
    if !mine && (runtime || not (Hashtbl.mem own n)) then (
      let q = qualified n in
      let modules, name =
        match String.rindex_opt q '/' with
        | Some i -> (String.split_on_char '.' (String.sub q 0 i), String.sub q (i + 1) (String.length q - i - 1))
        | None -> ([], q)
      in
      let base = internal n in
      let suffix = if String.starts_with ~prefix:base js then String.sub js (String.length base) (String.length js - String.length base) else "" in
      let path = modules @ [ property name ^ suffix ] in
      let path = if !compact then [ short keys next_key path ] else path in
      (* A name set! changes is read where it is used, through a getter. *)
      Hashtbl.replace exports path (if Hashtbl.find_opt how n = Some Compile.Cell then "get:" ^ js else js);
      vastra ^ "." ^ String.concat "." path)
    else js
  in
  let own_js n = if !compact then short shorts fresh n else camel (shown n) in
  let typed_copies = Hashtbl.create 4 and hoisted = Hashtbl.create 4 in
  let natives = Hashtbl.create 16 in
  let native n = Hashtbl.replace natives (internal n) (); reach ~runtime:true n (internal n) in
  (* Code that may change a buffer, or read one, or run what does something. *)
  let rec touches (e : expr) =
    (match e.kind with
    | Set _ | Update _ | Change _ | Send _ | Run _ | Await _ | Task_of _ -> true
    | Call { func = { kind = Var f; _ }; _ } -> String.ends_with ~suffix:"!" f || gives_task f
    | _ -> false)
    || (match e.typed with Type t -> maybe_buffer t | _ -> false)
    || List.exists touches (Ast.children e)
  in
  (* The program's small functions that run no loop are written out where they
     are called, and so is one called from one place that gives back a map. *)
  let entries =
    let calls, _ = uses entries and small = Hashtbl.create 16 and loops = Hashtbl.create 16 in
    List.iter
      (fun (top, _, _) ->
        match top with
        | Def { name = { name = n; _ }; value = { kind = Fn l; _ }; _ } when mentions n l.body -> Hashtbl.replace loops n ()
        | _ -> ())
      entries;
    List.iter
      (fun (top, _, _) ->
        match top with
        | Def { name = { name = n; _ }; value = { kind = Fn l; typed; _ }; _ }
          when Hashtbl.mem own n && Hashtbl.find_opt how n <> Some Compile.Cell && (not (gives_task n))
               && (not (String.ends_with ~suffix:"!" n)) && plain l.body && not (Hashtbl.mem loops n) ->
            let size = size l.body in
            if (size <= 30 && not (List.exists (Hashtbl.mem loops) (free l.body)))
               || (size <= 90 && Hashtbl.find_opt calls n = Some 1 && record_keys (exits "" l.body) <> None)
            then Hashtbl.replace small n (typed, l)
        | _ -> ())
      entries;
    let written scope e = floated ~touches (inline small [] scope e) in
    List.map
      (fun (top, outcome, shown) ->
        let top =
          match top with
          | Def ({ value = { kind = Fn l; _ } as v; _ } as d) ->
              let body = written (List.map (fun (b : binding) -> b.name) l.params) l.body in
              Def { d with value = { v with kind = Fn { l with body } } }
          | Def { value = { kind = Run _; _ }; _ } -> top
          | Def d -> Def { d with value = written [] d.value }
          | Expr e -> Expr (written [] e)
          | t -> t
        in
        (top, outcome, shown))
      entries
  in
  (* The program's functions nothing calls any more are left out. *)
  let entries =
    let bodies = Hashtbl.create 64 and live = Hashtbl.create 64 in
    List.iter
      (fun (top, _, _) ->
        match top with
        | Def { name; value = { kind = Fn _; _ } as v; _ } when Hashtbl.mem own name.name ->
            Hashtbl.replace bodies name.name v
        | _ -> ())
      entries;
    let rec reach (e : expr) =
      List.iter
        (fun n ->
          if Hashtbl.mem bodies n && not (Hashtbl.mem live n) then (
            Hashtbl.replace live n ();
            reach (Hashtbl.find bodies n)))
        (free e)
    in
    List.iter
      (fun (top, _, _) ->
        match top with
        | Def { name; _ } when Hashtbl.mem bodies name.name -> ()
        | Def { value = e; _ } | Expr e | On { handler = e; _ } -> reach e
        | View { place; draw; _ } -> reach place; reach draw
        | _ -> ())
      entries;
    let kept (top, _, _) = match top with Def { name = { name; _ }; _ } -> Hashtbl.mem live name || not (Hashtbl.mem bodies name) | _ -> true in
    (* --show shows every definition, used or not. *)
    if show then entries else List.filter kept entries
  in
  let entries =
    let typed t = is_buffer (Some t) && typed_array (element (Some t)) <> None in
    let go e = let_go typed [] (local_types e) in
    let go = function Def d -> Def { d with value = go d.value } | Expr e -> Expr (go e) | t -> t in
    List.map (fun (top, outcome, shown) -> (go top, outcome, shown)) entries
  in
  (* A program that lets no buffer go makes its buffers new, as it says. *)
  let keeps = List.exists (fun (top, _, _) -> match top with Def { value = e; _ } | Expr e -> mentions "#spare" e | _ -> false) entries in
  (* JavaScript grows its stack with every call, where Vastra doesn't for a
     function's last one. So a function whose last step calls a function not
     known by name hands that call back (runtime.js's next), and whoever uses
     the result settles it. These are the program's functions that may hand
     one back, the library's included: those, and those ending with a call to
     one of them. *)
  let bouncy = Hashtbl.create 16 in
  let functions =
    List.filter_map
      (fun (top, _, _) ->
        match top with
        | Def { name = { name = n; _ }; value = { kind = Fn l; _ } as v; _ } -> Some (n, free v, l)
        | _ -> None)
      entries
  in
  let rec settle_bouncy () =
    let hands_back (n, globals, (l : lambda)) =
      List.exists
        (fun (f : expr) ->
          match f.kind with
          | Var x when x = n -> false
          | Var x -> (not (List.mem x globals)) || Hashtbl.mem bouncy x
          | _ -> true)
        (last_calls l.body)
    in
    let fresh = List.filter (fun ((n, _, _) as f) -> (not (Hashtbl.mem bouncy n)) && hands_back f) functions in
    List.iter (fun (n, _, _) -> Hashtbl.replace bouncy n ()) fresh;
    if fresh <> [] then settle_bouncy ()
  in
  settle_bouncy ();
  let written = Hashtbl.create 64 in
  List.iter (fun (n, _, _) -> Hashtbl.replace written n ()) functions;
  (* A function generic over number gets a copy per number types it is used at. *)
  let generics = Hashtbl.create 16 in
  List.iter
    (fun (top, _, _) ->
      match top with
      | Def { name; value = { kind = Fn l; typed = Generic vars; _ }; _ } -> Hashtbl.replace generics name.name (vars, l)
      | _ -> ())
    entries;
  (* So does a function generic over other types, per the types it is called
     with, so its body knows how to print or compare what it is given. *)
  let poly = Hashtbl.create 16 in
  List.iter
    (fun (top, _, _) ->
      match top with
      | Def { name; value = { kind = Fn l; typed = Type (Fun _ as t); _ }; _ }
        when has_var t && Hashtbl.find_opt how name.name <> Some Compile.Cell ->
          Hashtbl.replace poly name.name (t, l)
      | _ -> ())
    entries;
  (* While a copy is printed, the types of its variables. *)
  let copying = ref [] and copies = Hashtbl.create 16 and wanted = Queue.create () in
  let resolve = function
    | Hidden v as n -> (
        match List.assoc_opt v !copying with Some (Types.Con (c, [])) -> Known (Num.of_name c) | _ -> n)
    | n -> n
  in
  let def_name n = if Hashtbl.mem own n then own_js n else internal n in
  let needed = Hashtbl.create 64 in
  let global n =
    if Hashtbl.mem generics n || Hashtbl.mem poly n then fail ("generic " ^ n ^ " used without its types")
    else (Hashtbl.replace needed n (); reach n (def_name n))
  in
  (* The copy of [n] for the types of its variables [subst]: the first is n itself. *)
  let instance n subst =
    let subst = List.sort compare subst in
    match Hashtbl.find_opt copies (n, subst) with
    | Some js -> js
    | None ->
        let count = Hashtbl.fold (fun (m, _) _ k -> if m = n then k + 1 else k) copies 0 in
        let base = if Hashtbl.mem own n then own_js n else internal n in
        let js = if count = 0 then base else base ^ string_of_int (count + 1) in
        Hashtbl.add copies (n, subst) js;
        Queue.add (n, subst, js) wanted;
        js
  in


  let ctor_js n = reach n (if Hashtbl.mem own n then own_js n else camel (tag n)) in
  (* Locals: their JavaScript names, fresh within a function. *)
  let taken = ref (Hashtbl.create 8) in
  let bind env n =
    if !compact then (let js = fresh () in ((n, js) :: env, js)) else
    let base = camel (base_name n) in
    let rec free i = let c = if i = 1 then base else base ^ string_of_int i in if Hashtbl.mem !taken c then free (i + 1) else c in
    let js = free 1 in
    Hashtbl.replace !taken js ();
    ((n, js) :: env, js)
  in
  (* An inner function takes fresh names, so it never hides one it uses. *)
  let in_function f = let saved = !taken in taken := Hashtbl.copy saved; let r = f () in taken := saved; r in
  let whole n = if Z.numbits n <= 53 then Z.to_string n else Z.to_string n ^ "n" in
  let literal (e : expr) n =
    match e.typed with
    | Literal t -> (
        match resolve t with
        | Known Num.Int -> whole n
        | Known Num.Float -> number (js_float (Z.to_float n))
        | Known (Num.Fixed f) -> Z.to_string (Num.to_z f (Num.of_z f n))
        | Hidden _ -> fail ("a literal of a type not known here"))
    | _ -> whole n
  in
  (* What the checker found an expression to be; a generic function's copy
     knows its number types. *)
  let type_of (e : expr) =
    let concrete = Infer.map_type (function Types.Var v as t -> Option.value (List.assoc_opt v !copying) ~default:t | t -> t) in
    match e.typed with
    | Type t -> Some (concrete t)
    | Literal t -> (match resolve t with Known n -> Some (Types.con (Num.name n)) | Hidden _ -> None)
    | Use [ t ] -> (match resolve t with Known n -> Some (Types.con (Num.name n)) | Hidden _ -> None)
    | _ -> None
  in
  let named t = match t with Some (Types.Con (c, _)) -> c | _ -> "" in
  (* A function's parameter types, as its body uses them. *)
  let params_of n =
    match Hashtbl.find_opt poly n with
    | Some (Types.Fun (ps, _, _), _) -> List.map Option.some ps
    | _ ->
        let l = snd (Hashtbl.find generics n) in
        List.map (fun (b : binding) -> find_var b.name l.body) l.params
  in
  (* The copy of [n] for this use: number types as the checker told them, the rest
     from the arguments [xs], or from the type of [f] when it is used as a value. *)
  let subst_for n (f : expr) xs =
    let numbers =
      match (f.typed, Hashtbl.find_opt generics n) with
      | Use ns, Some (vars, _) ->
          List.combine vars
            (List.map (fun t -> match resolve t with Known t -> Types.con (Num.name t) | Hidden _ -> fail ("types of " ^ n)) ns)
      | _ -> []
    in
    let others =
      match (xs, Hashtbl.find_opt poly n) with
      | None, Some (t, _) -> Option.fold (type_of f) ~none:[] ~some:(bind_types [] t)
      | Some xs, _ ->
          let params = params_of n in
          if List.length params <> List.length xs then []
          else
            List.fold_left2
              (fun acc p (x : expr) -> match (p, type_of x) with Some p, Some t -> bind_types acc p t | _ -> acc)
              [] params xs
      | None, None -> []
    in
    numbers @ List.filter (fun (v, _) -> not (List.mem_assoc v numbers)) others
  in
  let copy_for n f xs = instance n (subst_for n f xs) in
  (* An operator on Ints goes through the runtime, which turns to BigInt past 2^53. *)
  let on_ints (f : expr) =
    match f.typed with Use (t :: _) -> resolve t = Known Num.Int | _ -> false
  in
  (* The fixed width an operator works at: its bits are a JavaScript number's. *)
  let fixed_of (f : expr) =
    match f.typed with Use (t :: _) -> (match resolve t with Known (Num.Fixed x) -> Some x | _ -> None) | _ -> None
  in
  (* [code], kept to the bits of [fx], as JavaScript's 32-bit operations leave it. *)
  let wrapped fx (code, prec) =
    let inner level = paren level (code, prec) in
    match fx with
    | Num.U32 -> (p "%s >>> 0" (inner (shift + 1)), shift)
    | Num.I32 -> (p "%s | 0" (inner (bitor + 1)), bitor)
    | Num.U8 -> (p "%s & 255" (inner (bitand + 1)), bitand)
    | Num.U16 -> (p "%s & 65535" (inner (bitand + 1)), bitand)
    | Num.I8 -> (p "%s << 24 >> 24" (inner (shift + 1)), shift)
    | Num.I16 -> (p "%s << 16 >> 16" (inner (shift + 1)), shift)
  in
  let is_literal (e : expr) = match e.kind with Int _ | Hex _ | Float _ | Str _ | Bool _ -> true | _ -> false in
  (* The fields of maps defined at the top, as written: (get ambient :r) is 0.35. *)
  let records = Hashtbl.create 16 in
  List.iter
    (fun (top, _, _) ->
      match top with
      | Def { name; value = { kind = Record fs; _ }; _ } when Hashtbl.find_opt how name.name = Some Compile.Plain ->
          Hashtbl.replace records name.name fs
      | _ -> ())
    entries;
  let field env (e : expr) =
    match e.kind with
    | Get { key; record = { kind = Var n; _ } } | Read { target = { kind = Var n; _ }; path = [ Key (key, _) ] }
      when not (List.mem_assoc n env) ->
        Option.bind (Hashtbl.find_opt records n) (List.assoc_opt key)
    | _ -> None
  in
  (* Whether [e] ends in a call to [self], on some branch. *)
  let rec tail_calls self (e : expr) =
    match e.kind with
    | Call { func = { kind = Var n; _ }; _ } -> n = self
    | If { then_branch; else_branch; _ } -> tail_calls self then_branch || tail_calls self else_branch
    | Match { clauses; _ } -> List.exists (fun (_, b) -> tail_calls self b) clauses
    | Let { body; _ } | Par_let { body; _ } -> tail_calls self body
    | _ -> false
  in
  let rec closes (e : expr) = match e.kind with Fn _ -> true | _ -> List.exists closes (Ast.children e) in
  (* The type at [path] in a value of type [t], and whether it is a buffer. *)
  let rec at_path (t : Types.t option) path =
    match (t, path) with
    | t, [] -> t
    | Some (Types.Record row), Key (k, _) :: rest -> at_path (List.assoc_opt k (Types.fields row)) rest
    | Some (Types.Con ("Vector", [ a; _ ])), At _ :: rest -> at_path (Some a) rest
    | _ -> None
  in
  (* Keys only, none of them one that may be missing. *)
  let plain_keys = List.for_all (function Key (k, _) -> not (Util.may_miss k) | At _ -> false) in
  let keys_then_index path =
    match List.rev path with
    | At i :: keys -> if plain_keys keys then Some (List.rev keys, i) else None
    | _ -> None
  in
  (* Keys, then an index into a vector: not a dictionary's key. *)
  let vector_index (target : expr) path =
    match keys_then_index path with
    | Some (keys, _) as found when (match at_path (type_of target) keys with Some (Types.Con ("Vector", _)) -> true | _ -> false) -> found
    | _ -> None
  in
  let members keys = String.concat "" (List.map (function Key (k, _) -> member k | At _ -> "") keys) in
  (* A body's value is returned; unit needs none, and nothing at the end. *)
  let returns v = if v = "undefined" then [ "return;" ] else [ p "return %s;" v ] in
  let ending lines = match List.rev lines with "return;" :: rest -> List.rev rest | _ -> lines in

  (* The range of every number, found before printing, so an Int that stays a
     safe integer needs no BigInt and a clamp no test it cannot fail. A
     function's parameters take the ranges of every call to it, again and
     again until they settle; one that keeps growing grows to infinity. *)
  let module Nodes = Hashtbl.Make (struct type t = expr let equal = ( == ) let hash = Hashtbl.hash end) in
  let ranges = Nodes.create 1024 in
  let range_of e = Option.value (Nodes.find_opt ranges e) ~default:any in
  let fns = Hashtbl.create 64 in
  List.iter
    (fun (top, _, _) ->
      match top with
      | Def { name; value = { kind = Fn l; _ }; _ } when Hashtbl.find_opt how name.name <> Some Compile.Cell ->
          Hashtbl.replace fns name.name l
      | _ -> ())
    entries;
  let assumed = Hashtbl.create 64 and seen = Hashtbl.create 64 and rounds = Hashtbl.create 64 in
  let constants = Hashtbl.create 64 in
  let is_int e = named (type_of e) = "Int" || fixed_type (type_of e) <> None in
  let by_type e =
    match fixed_type (type_of e) with
    | Some f -> let lo, hi = Num.range f in within (Z.to_float lo) (Z.to_float hi)
    | None -> if named (type_of e) = "Int" then { any with nan = false } else any
  in
  let called n rs =
    let rs = match Hashtbl.find_opt seen n with Some old when List.length old = List.length rs -> List.map2 union old rs | _ -> rs in
    Hashtbl.replace seen n rs
  in
  let calls, as_value = uses entries in
  let rec rebinds x (e : expr) =
    (match e.kind with
    | Let { bindings; _ } | Par_let { bindings; _ } -> List.exists (fun ((b : binding), _) -> b.name = x) bindings
    | Fn l -> List.exists (fun (b : binding) -> b.name = x) l.params
    | Match { clauses; _ } -> List.exists (fun (pat, _) -> List.mem x (names pat)) clauses
    | _ -> false)
    || List.exists (rebinds x) (Ast.children e)
  in
  (* A loop's index counted up with its counter, that starts as the counter's
     start plus some a, is the counter plus a all along: called (f … x (+ a x))
     and calling itself (f … (inc x) (inc i)), i is x + a. *)
  let derived = Hashtbl.create 8 and sites = Hashtbl.create 64 in
  let rec walk self (e : expr) =
    (match e.kind with Call { func = { kind = Var n; _ }; args } -> Hashtbl.add sites n (n = self, args) | _ -> ());
    List.iter (walk self) (Ast.children e)
  in
  List.iter
    (fun (top, _, _) ->
      match top with
      | Def { name; value; _ } -> walk name.name value
      | Expr e | On { handler = e; _ } -> walk "" e
      | View { place; draw; _ } -> walk "" place; walk "" draw
      | _ -> ())
    entries;
  Hashtbl.iter
    (fun n (l : lambda) ->
      let ps = List.map (fun (b : binding) -> b.name) l.params in
      let self, outside = List.partition fst (Hashtbl.find_all sites n) in
      let counted i x (_, args) =
        match ((List.nth args i).kind, (List.nth args x).kind) with
        | ( Call { func = { kind = Var "inc"; _ }; args = [ { kind = Var a; _ } ] },
            Call { func = { kind = Var "inc"; _ }; args = [ { kind = Var b; _ } ] } )
        | Var a, Var b ->
            a = List.nth ps i && b = List.nth ps x
        | _ -> false
      in
      let start i x (_, args) =
        match ((List.nth args i).kind, (List.nth args x).kind) with
        | Call { func = { kind = Var "+"; _ }; args = [ a; b ] }, Var w when named (type_of a) = "Int" -> (
            match (a.kind, b.kind) with Var v, _ when v = w -> Some b | _, Var v when v = w -> Some a | _ -> None)
        | _ -> None
      in
      if outside <> [] && (not (Hashtbl.mem as_value n))
         && List.for_all (fun (_, args) -> List.length args = List.length ps) (self @ outside)
      then
        List.iteri
          (fun i p ->
            List.iteri
              (fun x q ->
                let starts = List.filter_map (start i x) outside in
                if i <> x && List.length starts = List.length outside && List.for_all (counted i x) self
                   && not (rebinds p l.body || rebinds q l.body)
                then Hashtbl.add derived n (p, q, starts, ref any))
              ps)
          ps)
    fns;
  let along = ref [] (* the derived indices of the function looked at *) in
  let offset (_, _, starts, _) =
    List.fold_left (fun r a -> union r (range_of a)) { lo = Float.infinity; hi = Float.neg_infinity; nan = false } starts
  in
  let rec range env (e : expr) =
    let r = range_kind env e in
    Nodes.replace ranges e r;
    r
  and range_kind env (e : expr) =
    let r = range env in
    match e.kind with
    | Int n | Hex n -> exact (Z.to_float n)
    | Float f -> exact f
    | Var n when List.mem_assoc n env -> (
        let r = List.assoc n env in
        match List.find_opt (fun (i, _, _, _) -> i = n) !along with
        | Some (_, x, _, a) when List.mem_assoc x env -> meet r (plus (List.assoc x env) !a)
        | _ -> r)
    | (Get _ | Read _) when field env e <> None -> range [] (Option.get (field env e))
    | Var n when Hashtbl.mem constants n -> Hashtbl.find constants n
    | Var n when Hashtbl.mem fns n ->
        (* A function as a value may be called with anything. *)
        called n (List.map (fun _ -> any) (Hashtbl.find fns n).params);
        any
    | If { condition; then_branch; else_branch } ->
        ignore (r condition);
        union (range (facts env condition true) then_branch) (range (facts env condition false) else_branch)
    | Let { bindings; body; how = h } ->
        let bind env ((b : binding), (v : expr)) =
          match (v.kind, h) with Fn _, Recursive -> ignore (range env v); (b.name, any) :: env | _ -> (b.name, range env v) :: env
        in
        range (List.fold_left bind env bindings) body
    | Par_let { bindings; body } -> range env { e with kind = Let { bindings; body; how = Names } }
    | Match { scrutinee; clauses } ->
        ignore (r scrutinee);
        let arm (pat, b) = range (List.map (fun n -> (n, any)) (names pat) @ env) b in
        (match List.map arm clauses with [] -> any | r :: rs -> List.fold_left union r rs)
    | Fn l -> ignore (range (List.map (fun (b : binding) -> (b.name, any)) l.params @ env) l.body); any
    | Call { func = { kind = Var n; _ }; args } when not (List.mem_assoc n env) -> apply e n args (List.map r args)
    | _ -> List.iter (fun c -> ignore (r c)) (Ast.children e); by_type e
  and apply e n args xs =
    let float = named (type_of e) = "Float" in
    (match Hashtbl.find_opt fns n with Some l when List.length l.params = List.length xs -> called n xs | _ -> ());
    match (n, xs, args) with
    | _ when fixed_type (type_of e) <> None -> by_type e
    | "+", [ a; b ], _ -> plus a b
    | "-", [ a; b ], _ -> minus a b
    | "*", [ a; _ ], [ { kind = Var x; _ }; { kind = Var y; _ } ] when x = y -> square a
    | "*", [ a; b ], _ -> times a b
    | "/", [ a; b ], _ when float -> divide a b
    | "inc", [ a ], _ -> plus a (exact 1.)
    | "dec", [ a ], _ -> minus a (exact 1.)
    | "macro/negate", [ a ], _ -> negate a
    | "floor", [ a ], _ -> { a with lo = Float.floor a.lo; hi = Float.floor a.hi }
    | "sqrt", [ a ], _ -> { lo = Float.sqrt (Float.max a.lo 0.); hi = Float.sqrt a.hi; nan = a.nan || a.lo < 0. }
    | ("min" | "max"), [ a; b ], _ ->
        (* NaN is ignored: one side may be all there is. *)
        let pick = if n = "min" then Float.min else Float.max in
        if a.nan || b.nan then { (union a b) with nan = a.nan && b.nan } else within (pick a.lo b.lo) (pick a.hi b.hi)
    | "to-float", [ a ], _ -> a
    | "to-int", [ a ], [ x ] when named (type_of x) = "Float" ->
        let t = { lo = Float.trunc a.lo; hi = Float.trunc a.hi; nan = false } in
        if a.nan || Float.abs a.lo = Float.infinity || Float.abs a.hi = Float.infinity then union t (exact 0.) else t
    | "to-int", [ a ], _ -> a
    | "count", _, _ -> within 0. 4294967295.
    | "option/or", [ _; d ], [ { kind = Call { func = { kind = Var "mod"; _ }; args = [ _; { kind = Int k; _ } ] }; _ }; _ ]
      when not (Z.equal k Z.zero) ->
        union (within 0. (Z.to_float (Z.pred (Z.abs k)))) d
    | "option/or", [ _; d ], _ -> union (by_type e) d
    | _ -> by_type e
  (* What [env] knows where [c] is [truth]. *)
  and facts env (c : expr) truth =
    let refine env (x : expr) r = match x.kind with Var n when List.mem_assoc n env -> (n, r) :: env | _ -> env in
    match c.kind with
    | Call { func = { kind = Var (("<" | ">" | "<=" | ">=") as op); _ }; args = [ a; b ] } ->
        let a, b, strict = match op with "<" -> (a, b, true) | ">" -> (b, a, true) | "<=" -> (a, b, false) | _ -> (b, a, false) in
        let int = is_int a and ra = range env a and rb = range env b in
        let ra, rb =
          if truth then order ~strict ~int ~sure:true ra rb
          else let rb, ra = order ~strict:(not strict) ~int ~sure:false rb ra in (ra, rb)
        in
        refine (refine env a ra) b rb
    | Call { func = { kind = Var "not"; _ }; args = [ x ] } -> facts env x (not truth)
    | If { condition; then_branch; else_branch = { kind = Bool false; _ } } when truth ->
        facts (facts env condition true) then_branch true
    | If { condition; then_branch = { kind = Bool true; _ }; else_branch } when not truth ->
        facts (facts env condition false) else_branch false
    | _ -> env
  in
  let pass () =
    Hashtbl.reset seen;
    Hashtbl.iter (fun _ ((_, _, _, a) as d) -> a := offset d) derived;
    List.iter
      (fun (top, _, _) ->
        match top with
        | Def { name; value = { kind = Fn l; _ }; _ } when Hashtbl.mem fns name.name -> (
            match Hashtbl.find_opt assumed name.name with
            | Some rs ->
                along := Hashtbl.find_all derived name.name;
                ignore (range (List.combine (List.map (fun (b : binding) -> b.name) l.params) rs) l.body);
                along := []
            | None -> ())
        | Def { name; value; _ } ->
            let r = range [] value in
            if Hashtbl.find_opt how name.name = Some Compile.Plain then Hashtbl.replace constants name.name r
        | Expr e | On { handler = e; _ } -> ignore (range [] e)
        | View { place; draw; _ } -> ignore (range [] place); ignore (range [] draw)
        | _ -> ())
      entries;
    Hashtbl.fold
      (fun n rs changed ->
        let next =
          match Hashtbl.find_opt assumed n with
          | None -> rs
          | Some old ->
              let k = Option.value (Hashtbl.find_opt rounds n) ~default:0 in
              Hashtbl.replace rounds n (k + 1);
              List.map2 (fun o r -> let j = union o r in if k >= 3 then widened o j else j) old rs
        in
        if Hashtbl.find_opt assumed n = Some next then changed else (Hashtbl.replace assumed n next; true))
      seen false
    || Hashtbl.fold (fun _ ((_, _, _, a) as d) moved -> moved || offset d <> !a) derived false
  in
  let rec settle k = if k = 0 then Nodes.reset ranges else if pass () then settle (k - 1) in
  settle 100;

  (* A loop called from one place is printed there, inside its caller: no call,
     and a record it gives back can be its fields instead. *)
  (* The arguments of each call [self] makes to itself at the end. *)
  let rec self_args self (e : expr) =
    match e.kind with
    | Call { func = { kind = Var n; _ }; args } when n = self -> [ args ]
    | If { then_branch; else_branch; _ } -> self_args self then_branch @ self_args self else_branch
    | Match { clauses; _ } -> List.concat_map (fun (_, b) -> self_args self b) clauses
    | Let { body; _ } | Par_let { body; _ } -> self_args self body
    | _ -> []
  in
  let loops = Hashtbl.create 16 in
  Hashtbl.iter
    (fun n (l : lambda) ->
      if tail_calls n l.body && (not (closes l.body)) && (not (gives_task n || Hashtbl.mem as_value n))
         && Hashtbl.find_opt calls n = Some (1 + List.length (self_args n l.body))
      then Hashtbl.replace loops n l)
    fns;
  let inlinable env (e : expr) =
    match e.kind with
    | Call { func = { kind = Var f; _ }; args } ->
        Hashtbl.mem loops f && (not (List.mem_assoc f env)) && List.length args = List.length (Hashtbl.find loops f).params
    | _ -> false
  in
  let rec inlines env (e : expr) =
    inlinable env e
    ||
    match e.kind with
    | If { then_branch; else_branch; _ } -> inlines env then_branch || inlines env else_branch
    | Let { body; _ } | Par_let { body; _ } -> inlines env body
    | Match { clauses; _ } -> List.exists (fun (_, b) -> inlines env b) clauses
    | _ -> false
  in
  (* [x] is only read for one of [keys]. *)
  let rec fields_only x keys (e : expr) =
    match e.kind with
    | Get { key; record = { kind = Var n; _ } } | Read { target = { kind = Var n; _ }; path = [ Key (key, _) ] }
      when n = x ->
        List.mem key keys
    | Var n -> n <> x
    | _ -> List.for_all (fields_only x keys) (Ast.children e)
  in
  let scalars = Hashtbl.create 8 in

  (* A vector of fixed-width numbers defined at the top, and only read by index,
     there or through a parameter only read so, is a typed array: a U8 a byte. *)
  let rec index_only x (e : expr) =
    match e.kind with
    | Call { func = { kind = Var ("nth" | "count"); _ }; args = { kind = Var n; _ } :: rest } when n = x ->
        List.for_all (index_only x) rest
    | Call { func = { kind = Var f; _ }; args } when Hashtbl.mem fns f && List.exists (fun (a : expr) -> a.kind = Var x) args ->
        let l = Hashtbl.find fns f in
        List.length args = List.length l.params
        && List.for_all2
             (fun (a : expr) (b : binding) ->
               match a.kind with
               | Var n when n = x -> (not (rebinds b.name l.body)) && index_only b.name l.body
               | _ -> index_only x a)
             args l.params
    | Var n -> n <> x
    | _ -> List.for_all (index_only x) (Ast.children e)
  in
  let columns = Hashtbl.create 4 in
  List.iter
    (fun (top, _, _) ->
      match top with
      | Def { name; value; _ }
        when Hashtbl.find_opt how name.name = Some Compile.Plain && (not (is_buffer (type_of value)))
             && fixed_type (element (type_of value)) <> None ->
          let read (top, _, _) =
            match top with
            | Def { value = e; _ } | Expr e | On { handler = e; _ } -> index_only name.name e
            | View { place; draw; _ } -> index_only name.name place && index_only name.name draw
            | _ -> true
          in
          if List.for_all read entries then
            Hashtbl.replace columns name.name (Option.get (typed_array (element (type_of value))))
      | _ -> ())
    entries;

  (* Whether [v], when it branches, prints as one expression. *)
  let one_expression env (v : expr) =
    match v.kind with
    | Match { scrutinee = { kind = Var n; _ }; clauses } ->
        (List.mem_assoc n env || not (Hashtbl.mem how n)) && List.for_all (fun (_, b) -> simple b) clauses
    | _ -> simple v
  in
  (* The buffers given to a loop that it writes into only at indices known to
     be from 0 to some hi, with that hi: written in place whatever, they are
     never replaced, and once longer than hi, need no test at each write. *)
  let guards self (l : lambda) params =
    List.filter_map
      (fun (k, (b : binding)) ->
        let top = ref Float.neg_infinity in
        let rec ok (e : expr) =
          match e.kind with
          | Set { target = { kind = Var q; _ } as t; path = [ At i ]; value } when q = b.name ->
              let r = range_of i in
              top := Float.max !top r.hi;
              is_buffer (type_of t) && r.lo >= 0. && r.hi < 4294967295. && ok i && ok value
          | Set { target = { kind = Var q; _ }; _ } when q = b.name -> false
          | Call { func = { kind = Var f; _ }; args } when f = self ->
              let passed j (a : expr) =
                if j <> k then ok a
                else match a.kind with Var q -> q = b.name | Set { target = { kind = Var q; _ }; _ } -> q = b.name && ok a | _ -> false
              in
              List.for_all Fun.id (List.mapi passed args)
          | Call { func = { kind = Var ("count" | "nth"); _ }; args = { kind = Var q; _ } :: rest } when q = b.name ->
              List.for_all ok rest
          | Call { args; _ } when List.exists (fun (a : expr) -> a.kind = Var b.name) args -> false
          | Fn _ -> not (mentions b.name e)
          | _ -> List.for_all ok (Ast.children e)
        in
        if (not (rebinds b.name l.body)) && ok l.body && !top >= 0. then Some (List.nth params k, !top) else None)
      (List.mapi (fun k b -> (k, b)) l.params)
  in
  let unguarded = ref [] in
  let bits_only = ref false in
  (* Set just before printing a function's last call: it isn't settled. *)
  let tail_call = ref false in
  let written_as = shown in
  (* Each type's text, a function made once and printed after the program. *)
  let show_helpers = Hashtbl.create 8 and helper_code = ref [] in
  let may_bounce env (f : expr) =
    match f.kind with
    | Keyword _ -> false
    | Var x when List.mem_assoc x env -> true
    | Var x when Hashtbl.mem how x || Analyze.is_upper (tag x) -> Hashtbl.mem bouncy x
    | _ -> true
  in
  (* A function value that may hand a call back, given to code that uses its result. *)
  let bounces env (f : expr) =
    match f.kind with
    | Keyword _ -> false
    | Fn l -> List.exists (may_bounce env) (last_calls l.body)
    | Var x when not (List.mem_assoc x env) -> Hashtbl.mem bouncy x
    | _ -> true
  in
  let natives_of_program = Hashtbl.create 64 in
  List.iter (fun (top, _, _) -> match top with Native { name; _ } -> Hashtbl.replace natives_of_program name.name () | _ -> ()) entries;
  (* A written type, as runtime.js's decode reads it. The constructors it
     names are used, though no code names them. *)
  let in_shapes = Hashtbl.create 4 in
  let rec shape_js (s : Shape.t) =
    match s with
    | Shape.Int -> "\"Int\""
    | Float -> "\"Float\""
    | String -> "\"String\""
    | Bool -> "\"Bool\""
    | Vector s -> p "{ vector: %s }" (shape_js s)
    | Option s -> p "{ option: %s }" (shape_js s)
    | Record keys -> p "{ record: [%s] }" (String.concat ", " (List.map (fun (k, s) -> p "[%s, %s]" (js_string k) (shape_js s)) keys))
    | Words words ->
        List.iter (fun (c, _) -> Hashtbl.replace in_shapes c ()) words;
        p "{ words: [%s] }" (String.concat ", " (List.map (fun (c, w) -> p "[%s, %s]" (js_string w) (ctor_js c)) words))
    | Json -> "\"Json\""
    | Message _ -> fail "a message from JavaScript"
  in
  let rec expr env (e : expr) : string * int =
    let tail = !tail_call in
    tail_call := false;
    let go ?(level = arrow) e = paren level (expr env e) in
    let args xs = List.map go xs in
    let steps path = String.concat ", " (List.map (function Key (k, _) -> js_string k | At i -> go i) path) in
    match e.kind with
    | Match { scrutinee = { kind = Var n; _ } as scrutinee; clauses }
      when (List.mem_assoc n env || not (Hashtbl.mem how n)) && (match e.typed with Decodes _ -> false | _ -> true) ->
        let it = fst (expr env scrutinee) in
        let arms =
          List.map
            (fun (pat, body) ->
              let tests, names = pattern it pat in
              (tests, body, List.map (fun (n, access) -> (n, access)) names @ env))
            clauses
        in
        if not (List.for_all (fun (_, (b : expr), _) -> simple b) arms) then
          (p "(() => {\n%s\n})()" (block (ending (stmts env e returns))), call)
        else
          let last = List.length arms - 1 in
          let rec chain i = function
            | [] -> ""
            | (tests, body, env) :: rest ->
                let b = paren ternary (expr env body) in
                if i = last || tests = [] then b
                else conditional (String.concat " && " tests) b (chain (i + 1) rest)
          in
          (chain 0 arms, if List.length arms = 1 then arrow else ternary)
    | (Let _ | Par_let _ | Match _ | If _) when not (simple e) ->
        (p "(() => {\n%s\n})()" (block (ending (stmts env e returns))), call)
    (* A task as a value: a generator function, run when it is called. *)
    | Call { func = { kind = Var ("task/and-then" | "task/succeed"); _ }; _ } ->
        (p "function* () {\n%s\n}" (block (ending (stmts ~task:true env e returns))), arrow)
    (* Code as data is its text: all a built program does with it is show it. *)
    | Quote n -> (js_string (Reader.to_source n), atom)
    | Int n | Hex n -> (literal e n, atom)
    | Float f -> ((if f < 0. then "(" ^ number (js_float f) ^ ")" else number (js_float f)), atom)
    | Bool b -> (string_of_bool b, atom)
    | Str s -> (js_string s, atom)
    | Var n when List.mem_assoc n env -> (List.assoc n env, atom)
    | Var n when Analyze.is_upper (tag n) -> (ctor_js n, atom)
    | Var "unit" -> ("undefined", atom)
    | Var n when Hashtbl.mem generics n || Hashtbl.mem poly n -> (reach n (copy_for n e None), atom)
    | Var (("+" | "-" | "*") as n) when on_ints e -> (native (int_op n), atom)
    | Var n -> (
        match operator n with
        | Some op ->
            let _, a = bind env "a" in
            let _, b = bind env "b" in
            (p "(%s, %s) => %s %s %s" a b a op b, arrow)
        | None -> (
            let fn_type =
              match (type_of e, e.typed) with
              | Some (Types.Fun _ as t), _ -> Some t
              | _, Use ns -> (
                  let known t = match resolve t with Known k -> Some (Types.con (Num.name k)) | Hidden _ -> None in
                  match (Infer.Env.find_opt n s.state.env.vars, List.map known ns) with
                  (* Told its number variables only, in order; the others stay. *)
                  | Some scheme, ts when List.for_all Option.is_some ts
                                         && List.length ts = List.length (List.filter Types.told (Array.to_list scheme.vars)) ->
                      let rec fill i ts =
                        if i = Array.length scheme.vars then []
                        else if Types.told scheme.vars.(i) then List.hd ts :: fill (i + 1) (List.tl ts)
                        else Types.Gen i :: fill (i + 1) ts
                      in
                      Some (given (fill 0 (List.map Option.get ts)) scheme.ty)
                  | _ -> None)
              | _ -> None
            in
            match fn_type with
            (* A native given as a value: a function that calls it as a call is
               written, with the types it is used at. *)
            | Some (Types.Fun (params, _, _)) when Hashtbl.mem natives_of_program n && not (gives_task n) ->
                let names = List.mapi (fun i t -> (p "#arg~%d" i, t)) params in
                let inner, js = List.fold_left (fun (env, js) (a, _) -> let env, j = bind env a in (env, js @ [ j ])) (env, []) names in
                let args = List.map (fun (a, t) -> { e with kind = Var a; typed = Type t }) names in
                (p "(%s) => %s" (String.concat ", " js) (paren ternary (native_call inner n e args)), arrow)
            | _ -> (value_of n, atom)))
    | Vector xs -> (layout "[" (args xs) "]", atom)
    | Record fields ->
        let one = List.map (fun (k, v) -> match go v with js when js = k -> js | js -> p "%s: %s" (key k) js) fields in
        let line = "{ " ^ String.concat ", " one ^ " }" in
        if String.length line <= 72 then (line, atom) else (layout "{" one "}", atom)
    | Get { key = k; record = { kind = Var n; _ } } | Read { target = { kind = Var n; _ }; path = [ Key (k, _) ] }
      when List.mem_assoc n env && Hashtbl.mem scalars (List.assoc n env) ->
        let v = List.assoc k (Hashtbl.find scalars (List.assoc n env)) in
        if Util.may_miss k then (p "%s(%s)" (native "maybe") v, call) else (v, atom)
    | (Get _ | Read _) when Option.fold (field env e) ~none:false ~some:is_literal -> expr env (Option.get (field env e))
    | Get { key = k; record } when Util.may_miss k -> (p "%s(%s%s)" (native "maybe") (go ~level:call record) (member k), call)
    | Get { key = k; record } -> (go ~level:call record ^ member k, call)
    | Read { target; path } -> (
        match vector_index target path with
        | Some (keys, i) -> (p "%s(%s%s, %s)" (native "at") (go ~level:call target) (members keys) (go i), call)
        | None when plain_keys path ->
            (go ~level:call target ^ members path, call)
        | None when (match path with [ Key (k, _) ] -> Util.may_miss k | _ -> false) ->
            (p "%s(%s%s)" (native "maybe") (go ~level:call target) (members path), call)
        | None -> (p "%s(%s, [%s])" (native "get-path") (go target) (steps path), call))
    (* A buffer changes in place: no one else holds it. *)
    | Set { target; path; value }
      when buffer_chain e <> None
           || Option.fold (keys_then_index path) ~none:false ~some:(fun (keys, _) -> is_buffer (at_path (type_of target) keys)) -> (
        match (keys_then_index path, buffer_chain e) with
        | Some ([], i), _ -> (
            let b = go ~level:call target and at = go i and v = go value in
            if List.mem b !unguarded then (p "(%s[%s] = %s, %s)" b at v b, atom)
            else
            match inside env b i with
            | Some test when brief v -> (p "%s ? (%s[%s] = %s, %s) : %s(%s, %s, %s)" test b at v b (native "put") b at v, ternary)
            | _ -> (p "%s(%s, %s, %s)" (native "put") b at v, call))
        | _, Some (({ kind = Var _; _ } as base), steps) ->
            let b = go ~level:call base in
            (layout ~trailing:false "(" (List.map (write env b) steps @ [ b ]) ")", atom)
        | _, Some (base, steps) ->
            (* What is not a name is named, so it is computed once. *)
            let _, m = bind env "it" in
            (p "((%s) => (%s))(%s)" m (String.concat ", " (List.map (write env m) steps @ [ m ])) (go base), call)
        | _ -> fail "a buffer set inside what is not a name")
    | Set { target; path; value } when plain_keys path ->
        let rec set target = function
          | [ Key (k, _) ] -> p "{ ...%s, %s: %s }" target (key k) (go value)
          | Key (k, _) :: rest -> p "{ ...%s, %s: %s }" target (key k) (set (target ^ member k) rest)
          | _ -> fail "a path of keys"
        in
        (set (go ~level:call target) path, atom)
    (* An index, a dictionary's key, or a key that may be missing, on the way. *)
    | Set { target; path; value } ->
        let v = go value in
        (* { would open a block. *)
        let v = if String.starts_with ~prefix:"{" v then "(" ^ v ^ ")" else v in
        (p "%s(%s, [%s], () => %s, true)" (native "change") (go target) (steps path) v, call)
    | Update { target; path; func } ->
        let f = if bounces env func then p "%s(%s)" (native "settled") (go func) else go func in
        (p "%s(%s, [%s], %s, false)" (native "change") (go target) (steps path) f, call)
    | Fn l ->
        in_function (fun () ->
            let env, params = List.fold_left (fun (env, ps) (b : binding) -> let env, js = bind env b.name in (env, ps @ [ js ])) (env, []) l.params in
            let params = "(" ^ String.concat ", " params ^ ")" in
            if simple l.body && not (List.exists (may_bounce env) (last_calls l.body)) then
              let body = paren ternary (expr env l.body) in
              (* { would open a block. *)
              (p "%s => %s" params (if String.starts_with ~prefix:"{" body then "(" ^ body ^ ")" else body), arrow)
            else (p "%s => {\n%s\n}" params (block (ending (stmts ~back:true env l.body returns))), arrow))
    | If { condition; then_branch; else_branch } -> (
        match (then_branch.kind, else_branch.kind) with
        | _, Bool false -> (go ~level:and_ condition ^ " && " ^ go ~level:(and_ + 1) then_branch, and_)
        | Bool true, _ -> (go ~level:or_ condition ^ " || " ^ go ~level:(or_ + 1) else_branch, or_)
        | _ -> (conditional (go ~level:(ternary + 1) condition) (go ~level:ternary then_branch) (go ~level:ternary else_branch), ternary))
    | Call { func = { kind = Var n; _ }; args = xs } when Analyze.is_upper (tag n) && not (List.mem_assoc n env) ->
        (layout (ctor_js n ^ "(") (args xs) ")", call)
    | Call { func = { kind = Var n; _ } as f; args = xs } when not (List.mem_assoc n env) -> (
        let task = gives_task n in
        let settled (x : expr) = { x with kind = Call { func = { x with kind = Var "#settled" }; args = [ x ] } } in
        (* A function written in Vastra settles what it calls itself; a native doesn't. *)
        let xs =
          if Hashtbl.mem written n || String.starts_with ~prefix:"#" n then xs
          else List.map (fun (x : expr) -> match type_of x with Some (Types.Fun _) when bounces env x -> settled x | _ -> x) xs
        in
        let code = native_call env n f xs in
        (* A print is written as console.log, which gives no task to run. *)
        if task && n = "vastra.console/print" then (p "function* () {\n%s;\n}" (fst code), arrow)
        else if task then (p "() => %s" (paren ternary code), arrow)
        else if Hashtbl.mem bouncy n && not tail then (p "%s(%s)" (native "settle") (fst code), call)
        else code)
    | Call { func = { kind = Keyword k; _ }; args = [ r ] } when not (Util.may_miss k) -> (go ~level:call r ^ member k, call)
    | Call { func = { kind = Keyword k; _ }; args = [ r ] } -> (p "%s(%s%s)" (native "maybe") (go ~level:call r) (member k), call)
    | Keyword k when not (Util.may_miss k) -> (p "(r) => r%s" (member k), arrow)
    | Keyword k -> (p "(r) => %s(r%s)" (native "maybe") (member k), arrow)
    | Call { func; args = xs } when tail -> (p "%s(%s, [%s])" (native "next") (go func) (String.concat ", " (args xs)), call)
    | Call { func; args = xs } -> (p "%s(%s)" (native "settle") (layout (go ~level:call func ^ "(") (args xs) ")"), call)
    | Task_of x -> expr env x
    | Change { target = { kind = Var n; _ }; value } -> (p "%s = %s" (global n) (go value), arrow)
    | Send x -> (p "%s(%s)" (native "send") (go x), call)
    | _ -> fail "this form"
  (* One write of a chain, into the map [b]: an element of a buffer, or a key. *)
  and write env b (path, value) =
    match keys_then_index path with
    | Some (keys, i) ->
        let c = b ^ members keys in
        let at = fst (expr env i) and v = fst (expr env value) in
        let slow = p "%s = %s(%s, %s, %s)" c (native "put") c at v in
        if List.mem c !unguarded then p "%s[%s] = %s" c at v
        else (match inside env c i with Some test when brief v -> p "%s ? %s[%s] = %s : %s" test c at v slow | _ -> slow)
    | None -> p "%s%s = %s" b (members path) (fst (expr env value))
  and brief v = String.length v <= 24 && not (String.contains v '\n')
  (* Writes along [steps] as statements, from [q]; a long value is named first. *)
  and writes_into env q steps =
    List.concat_map
      (fun (path, (value : expr)) ->
        let v = fst (expr env value) in
        if brief v then [ write env q (path, value) ^ ";" ]
        else
          let env, js = bind env "#value" in
          [ p "const %s = %s;" js v; write env q (path, { value with kind = Var "#value" }) ^ ";" ])
      steps
  (* The test that index [i] is inside buffer [b], when [b] and [i] may be written
     more than once: a write is inline where it is, and put is left for the end,
     where it makes the buffer one longer, or past it, where it changes nothing. *)
  and inside env b (i : expr) =
    let at = fst (expr env i) in
    let calls = Str.string_match (Str.regexp ".*[A-Za-z0-9_$)](") at 0 in
    if String.contains b '(' || String.contains at '\n' || calls then None
    else if (range_of i).lo >= 0. then Some (p "%s < %s.length" at b)
    else Some (p "%s >= 0 && %s < %s.length" at at b)
  (* Writes into buffers along keys, one after the other, from a name: the name
     and each write, in order. *)
  and buffer_chain (e : expr) =
    let writes (e : expr) =
      match e.kind with
      | Set { target; path = [ Key (k, _) ]; _ } -> (not (Util.may_miss k)) && holds_buffer (type_of target)
      | Set { target; path; _ } ->
          Option.fold (keys_then_index path) ~none:false ~some:(fun (keys, _) -> keys <> [] && is_buffer (at_path (type_of target) keys))
      | _ -> false
    in
    let rec chain (e : expr) acc =
      match e.kind with Set { target; path; value } when writes e -> chain target ((path, value) :: acc) | _ -> (e, acc)
    in
    if writes e then Some (chain e []) else None
  (* A call to a global: inline when JavaScript has it, else a function. *)
  and native_call env n f xs =
    let go ?(level = arrow) e = paren level (expr env e) in
    let args xs = List.map go xs in
    (* Read by a bitwise operation, a 32-bit result needs no >>> 0 or | 0 of its
       own: the operation takes its 32 bits however they come. *)
    let raw = !bits_only in
    bits_only := false;
    let wrapped fx code = if raw && (fx = Num.U32 || fx = Num.I32) then code else wrapped fx code in
    let bits ~level (a : expr) =
      (match a.kind with
      | Call { func = { kind = Var m; _ }; _ }
        when (not (List.mem_assoc m env))
             && List.mem m [ "+"; "-"; "*"; "bit/and"; "bit/or"; "bit/xor"; "bit/not"; "bit/shift-left"; "to-u32"; "to-i32" ] ->
          bits_only := true
      | _ -> ());
      let s = go ~level a in
      bits_only := false;
      s
    in
    let small (x : expr) = match x.kind with Int k | Hex k -> Z.geq k Z.zero && Z.lt k (Z.of_int 0x80000000) | _ -> false in
    (* A value going to JavaScript: a JavaScript value as it is, any other encoded. *)
    let js_value (x : expr) =
      match type_of x with
      | Some (Types.Con (k, [])) when unversioned k = "vastra.js/Value" -> expr env x
      | _ -> (p "%s(%s)" (native "encode") (go x), call)
    in
    (* A function JavaScript's own map calls: what it hands back is settled there. *)
    let given f = if bounces env f then p "%s(%s)" (native "settled") (go f) else go f in
    let binary op prec = function
      | [ a; b ] -> (p "%s %s %s" (go ~level:prec a) op (go ~level:(prec + 1) b), prec)
      | _ -> fail ("arguments of " ^ n)
    in
    match (n, xs) with
    | "option/or", [ ({ kind = Read { target; path }; _ } as r); d ]
      when vector_index target path <> None
           && (match type_of r with Some (Types.Con ("Option", [ t ])) -> t <> Types.unit | _ -> false) ->
        let keys, i = Option.get (vector_index target path) in
        (p "%s%s[%s] ?? %s" (go ~level:call target) (members keys) (go i) (go ~level:(or_ + 1) d), ternary)
    | "option/or", [ { kind = Call { func = { kind = Var (("mod" | "quot") as op); _ }; args = [ a; ({ kind = Int k; _ } as b) ] }; _ }; _ ]
      when not (Z.equal k Z.zero) ->
        let r = range_of a in
        if Z.gt k Z.zero && r.lo >= 0. && safe r && (op = "mod" || int32 r) then
          if op = "mod" then (p "%s %% %s" (go ~level:mul a) (go ~level:(mul + 1) b), mul)
          else (p "Math.floor(%s / %s)" (go ~level:mul a) (go ~level:(mul + 1) b), call)
        else
          let code = (p "%s(%s, %s)" (native (if op = "mod" then "remainder" else "quotient")) (go a) (go b), call) in
          Option.fold (fixed_type (type_of a)) ~none:code ~some:(fun fx -> wrapped fx code)
    (* A signed width's lowest number over -1 wraps, as -128 / -1 does in an I8. *)
    | "quot", [ a; b ] when (match fixed_type (type_of a) with Some fx -> Num.signed fx | None -> false) ->
        (p "%s(%s, %s, %d)" (native "quot-signed") (go a) (go b) (Num.bits (Option.get (fixed_type (type_of a)))), call)
    | "option/or", [ ({ kind = Call { func = { kind = Var "nth"; _ }; args = [ xs; i ] }; _ } as r); d ]
      when (match type_of r with Some (Types.Con ("Option", [ t ])) -> t <> Types.unit | _ -> false) ->
        (p "%s[%s] ?? %s" (go ~level:call xs) (go i) (go ~level:(or_ + 1) d), ternary)
    | ("inc" | "dec"), [ x ] when named (type_of x) = "Int" && safe ((if n = "inc" then plus else minus) (range_of x) (exact 1.)) ->
        (p "%s %s 1" (go ~level:add x) (if n = "inc" then "+" else "-"), add)
    | ("inc" | "dec"), [ x ] when named (type_of x) = "Int" -> (p "%s(%s, 1)" (native (if n = "inc" then "add" else "sub")) (go x), call)
    | ("inc" | "dec"), [ x ] when named (type_of x) = "Float" -> (p "%s %s 1" (go ~level:add x) (if n = "inc" then "+" else "-"), add)
    | _ when Hashtbl.mem generics n || Hashtbl.mem poly n -> (layout (reach n (copy_for n f (Some xs)) ^ "(") (args xs) ")", call)
    | ("+" | "-"), [ a; b ] when fixed_of f <> None ->
        wrapped (Option.get (fixed_of f)) (p "%s %s %s" (go ~level:add a) n (go ~level:(add + 1) b), add)
    | "*", [ a; b ] when fixed_of f <> None ->
        let fx = Option.get (fixed_of f) in
        let product = (p "Math.imul(%s, %s)" (bits ~level:arrow a) (bits ~level:arrow b), call) in
        if fx = Num.I32 then product else wrapped fx product
    | ("bit/and" | "bit/or" | "bit/xor"), [ a; b ] when fixed_of f <> None ->
        let op, prec = match n with "bit/and" -> ("&", bitand) | "bit/or" -> ("|", bitor) | _ -> ("^", bitxor) in
        let code = (p "%s %s %s" (bits ~level:prec a) op (bits ~level:(prec + 1) b), prec) in
        (* A mask below 2^31 leaves no sign to undo. *)
        (match Option.get (fixed_of f) with
        | Num.U32 when not (n = "bit/and" && (small a || small b)) -> wrapped Num.U32 code
        | _ -> code)
    | "bit/not", [ a ] when fixed_of f <> None ->
        let fx = Option.get (fixed_of f) in
        let code = ("~" ^ bits ~level:unary a, unary) in
        if Num.signed fx then code else wrapped fx code
    | ("bit/shift-left" | "bit/shift-right"), [ a; { kind = Int k; _ } ] when fixed_of f <> None && Z.lt k (Z.of_int 32) && Z.geq k Z.zero ->
        let fx = Option.get (fixed_of f) in
        if n = "bit/shift-left" then wrapped fx (p "%s << %s" (bits ~level:shift a) (Z.to_string k), shift)
        else (p "%s %s %s" (bits ~level:shift a) (if Num.signed fx then ">>" else ">>>") (Z.to_string k), shift)
    (* By an amount known only when it runs: the width's bits kept, as in C. *)
    | ("bit/shift-left" | "bit/shift-right"), [ a; b ] when fixed_of f <> None ->
        let fx = Option.get (fixed_of f) in
        (p "%s(%s, %s, %d, %b, %b)" (native "shift-fixed") (go a) (go b) (Num.bits fx) (Num.signed fx) (n = "bit/shift-left"), call)
    | ("to-u8" | "to-u16" | "to-u32" | "to-i8" | "to-i16" | "to-i32"), [ x ] -> (
        let fx = match Num.of_name (String.uppercase_ascii (String.sub n 3 (String.length n - 3))) with Num.Fixed f -> f | _ -> assert false in
        match (x.kind, type_of x) with
        | (Int k | Hex k), _ -> (Z.to_string (Num.to_z fx (Num.of_z fx k)), atom)
        (* (floor v) of a name: the clamp written out, as a hot loop wants it. NaN
           and the infinities give 0, and floor stays within whole bounds. *)
        | Call { func = { kind = Var "floor"; _ }; args = [ ({ kind = Var _; _ } as v) ] }, _ ->
            let r = range_of v and lo, hi = Num.range fx and v = go ~level:atom v in
            let floor = p "Math.floor(%s)" v in
            let past bound infinity = if Float.is_finite infinity then bound else p "(%s === %s ? 0 : %s)" v (js_float infinity) bound in
            let upper =
              if r.hi < Z.to_float hi then floor
              else p "%s >= %s ? %s : %s" v (Z.to_string hi) (past (Z.to_string hi) r.hi) floor
            in
            if r.lo >= Z.to_float lo && not r.nan then (upper, if upper = floor then call else ternary)
            else if Z.equal lo Z.zero then (p "%s >= 0 ? %s : 0" v upper, ternary)
            else (p "%s !== %s ? 0 : %s <= %s ? %s : %s" v v v (Z.to_string lo) (past (Z.to_string lo) r.lo) upper, ternary)
        | _, Some (Types.Con ("Float", [])) ->
            let lo, hi = Num.range fx in
            (p "%s(%s, %s, %s)" (native "clamp-whole") (go x) (Z.to_string lo) (Z.to_string hi), call)
        | _, t when fixed_type t <> None -> wrapped fx (go ~level:atom x, atom)
        | _ -> wrapped fx (p "%s(%s)" (native "low-bits") (go x), call))
    | "to-int", [ x ] when named (type_of x) = "Float" -> (
        (* A whole Float in range is its Int; | 0 also gives NaN as 0. *)
        let r = range_of x in
        let whole = match x.kind with Call { func = { kind = Var "floor"; _ }; _ } -> true | _ -> false in
        match () with
        | () when safe r -> if whole then expr env x else (p "Math.trunc(%s)" (go x), call)
        | () when int32 r -> (p "%s | 0" (go ~level:(bitor + 1) x), bitor)
        | () -> (p "%s(%s)" (native "whole-part") (go x), call))
    | "to-int", [ x ] -> expr env x
    | "floor", [ x ] -> (p "Math.floor(%s)" (go x), call)
    | "abs", [ x ] when named (type_of x) = "Float" -> (p "Math.abs(%s)" (go x), call)
    | "abs", [ x ] -> (
        let code = (p "%s(%s)" (native "abs") (go x), call) in
        match fixed_type (type_of x) with Some fx when Num.signed fx -> wrapped fx code | _ -> code)
    | ("min" | "max"), [ a; b ]
      when (named (type_of a) = "Float" && not ((range_of a).nan || (range_of b).nan)) || (safe (range_of a) && safe (range_of b)) ->
        (p "Math.%s(%s, %s)" n (go a) (go b), call)
    | ("min" | "max"), [ a; b ] ->
        let which = if named (type_of a) = "Float" then n ^ "-float" else if n = "min" then "least" else "most" in
        (p "%s(%s, %s)" (native which) (go a) (go b), call)
    | "string/hex", [ x ] when fixed_type (type_of x) <> None ->
        (p "%s(%s, %d)" (native "hex") (go x) (Num.bits (Option.get (fixed_type (type_of x)))), call)
    | ("+" | "-" | "*"), [ a; b ] when on_ints f ->
        let ra = range_of a and rb = range_of b in
        let r = match n with "+" -> plus ra rb | "-" -> minus ra rb | _ -> times ra rb in
        if safe ra && safe rb && safe r then binary n (precedence n) xs
        else (p "%s(%s, %s)" (native (int_op n)) (go a) (go b), call)
    | ("+" | "-" | "*" | "/" | "<" | ">" | "<=" | ">="), _ -> binary (Option.get (operator n)) (precedence n) xs
    | "string-append", [ a; b ] -> (p "%s + %s" (go ~level:add a) (go ~level:add b), add)
    | ("=" | "not="), [ a; b ]
      when is_literal a || is_literal b
           || List.mem (named (type_of a)) [ "Int"; "Float"; "String"; "Bool"; "Unit" ]
           || fixed_type (type_of a) <> None ->
        binary (if n = "=" then "===" else "!==") eq xs
    | "=", [ a; b ] -> (p "%s(%s, %s)" (native "equal") (go a) (go b), call)
    | "not=", _ -> (p "!%s" (paren unary (native_call env "=" f xs)), unary)
    | "macro/negate", [ x ] ->
        (* --x would be a decrement; a fixed width wraps, as -(-128) does in an I8. *)
        let v = go ~level:unary x in
        let negated = ((if String.starts_with ~prefix:"-" v then p "-(%s)" v else "-" ^ v), unary) in
        Option.fold (fixed_type (type_of x)) ~none:negated ~some:(fun fx -> wrapped fx negated)
    | "not", [ x ] -> ("!" ^ go ~level:unary x, unary)
    | "to-float", [ x ] when safe (range_of x) || fixed_type (type_of x) <> None -> expr env x
    | "to-float", [ x ] -> (p "Number(%s)" (go x), call)
    | "to-string", [ x ] when named (type_of x) = "String" -> expr env x
    | "to-string", [ x ] ->
        (shown ~quoted:false (type_of x) (go x), call)
    | "pr-str", [ x ] -> (shown ~quoted:true (type_of x) (go x), call)
    | "count", [ xs ] -> (p "%s.length" (go ~level:call xs), call)
    | "empty?", [ xs ] -> (p "%s.length === 0" (go ~level:call xs), eq)
    (* par/ gives what map and filter give; here its parts run one after another. *)
    | ("map" | "par/map"), [ f; xs ] -> (layout (go ~level:call xs ^ ".map(") [ given f ] ")", call)
    | ("filter" | "par/filter"), [ f; xs ] -> (layout (go ~level:call xs ^ ".filter(") [ given f ] ")", call)
    | "reduce", [ f; init; xs ] -> (layout (go ~level:call xs ^ ".reduce(") [ given f; go init ] ")", call)
    | "string/fixed", [ x; { kind = Int d; _ } ] -> (p "%s.toFixed(%s)" (go ~level:call x) (Z.to_string d), call)
    | "string/trim", [ x ] -> (p "%s(%s)" (native "string/trim") (go x), call)
    | "sqrt", [ x ] -> (p "Math.sqrt(%s)" (go x), call)

    | "#spare", [ b ] -> (p "%s(%s)" (native "spare") (go b), call)
    (* What JavaScript gives back is decoded by the type on its let, if any. *)
    | ("vastra.js/global" | "vastra.js/get" | "vastra.js/call*" | "vastra.js/method*" | "vastra.js/new*" | "vastra.http/get"), _ ->
        let shape = match f.typed with Told_type s -> shape_js s | _ -> "null" in
        (layout (value_of n ^ "(") (shape :: args xs) ")", call)
    | "vastra.js/value", [ x ] -> js_value x
    | "vastra.js/set", [ o; k; v ] -> (layout (value_of n ^ "(") [ go o; go k; fst (js_value v) ] ")", call)
    | "vastra.js/reply", [ x ] -> expr env x
    | "#settled", [ f ] -> (p "%s(%s)" (native "settled") (go f), call)
    | "buffer/repeat", [ n; x ] when typed_array (type_of x) <> None ->
        (p "new %s(%s).fill(%s)" (Option.get (typed_array (type_of x))) (go n) (go x), call)
    | "buffer/repeat", [ n; x ] -> (p "new Array(%s).fill(%s)" (go n) (go x), call)
    (* A vector defined once at the top is copied into a typed array once, and a
       buffer made from it each time copies that, in one block. *)
    | "buffer/from", [ ({ kind = Var v; _ } as xs) ]
      when typed_array (element (type_of xs)) <> None && not (List.mem_assoc v env)
           && Hashtbl.mem own v && Hashtbl.find_opt how v = Some Compile.Plain ->
        let made = short typed_copies (fun () -> if !compact then fresh () else global v ^ "Typed") v in
        Hashtbl.replace hoisted v (made, Option.get (typed_array (element (type_of xs))));
        if keeps then (p "%s(%s)" (native "copied") made, call) else (made ^ ".slice()", call)
    | "buffer/from", [ xs ] when typed_array (element (type_of xs)) <> None ->
        (p "%s.from(%s)" (Option.get (typed_array (element (type_of xs)))) (go xs), call)
    | "buffer/from", [ xs ] | ("buffer/freeze" | "buffer/to-vector"), [ xs ] -> (p "Array.from(%s)" (go xs), call)
    | "vastra.html/child", [ ({ kind = Call { func = { kind = Var ("vastra.html/text" | "vastra.html/element"); _ }; _ }; _ } as x) ] ->
        ("[" ^ go x ^ "]", atom)
    | "vector/concat", [ a; b ] ->
        let rec spread (e : expr) =
          match e.kind with
          | Vector xs -> List.map go xs
          | Call { func = { kind = Var "vector/concat"; _ }; args = [ a; b ] } -> spread a @ spread b
          | Call { func = { kind = Var "vastra.html/child"; _ }; args = [ ({ kind = Call { func = { kind = Var ("vastra.html/text" | "vastra.html/element"); _ }; _ }; _ } as x) ] } -> [ go x ]
          | _ -> [ "..." ^ go ~level:call e ]
        in
        (layout "[" (spread a @ spread b) "]", atom)
    | "vastra.console/print", [ x ] -> (p "console.log(%s)" (go x), call)
    | _ -> (layout (value_of n ^ "(") (args xs) ")", call)
  and int_op = function "+" -> "add" | "-" -> "sub" | _ -> "mul"
  and operator = function
    | ("+" | "-" | "*" | "/" | "<" | ">" | "<=" | ">=") as op -> Some op
    | _ -> None
  and precedence = function "*" | "/" -> mul | "+" | "-" -> add | _ -> rel
  (* A value as text, by its type, as vastra run writes it: at run time 5 and
     5.0 are the same number. [names]: constructors as the program's file wrote
     them, as --show writes them; else unqualified, as to-string does. *)
  and shown ?(names = false) ~quoted t code =
    let apply f code =
      match f with
      | "String" -> p "String(%s)" code
      | f when String.starts_with ~prefix:"(" f -> p "(%s)(%s)" f code
      | f -> p "%s(%s)" f code
    in
    let rec show t =
      match t with
      | Some (Types.Con (("Int" | "Bool"), [])) -> "String"
      | Some t when fixed_type (Some t) <> None -> "String"
      | Some (Types.Con ("Float", [])) -> native "show-float"
      | Some (Types.Con ("String", [])) -> if quoted then native "quote" else "String"
      | Some (Types.Con ("Unit", [])) -> "() => \"unit\""
      | Some (Types.Con ("Task", _)) -> "() => \"#<task>\""
      | Some (Types.Con ("Running", [])) -> "() => \"#<running>\""
      | Some (Types.Con ("Form", [])) -> "(f) => \"'\" + f"
      | Some (Types.Fun _) -> "() => \"#<fn>\""
      | Some (Types.Con ("Vector", [ a; _ ])) ->
          p "(xs) => \"[\" + Array.from(xs, %s).join(\" \") + \"]\"" (with_quotes a)
      | Some (Types.Con ("Dict", [ k; v ])) ->
          p "(d) => \"{\" + d.entries.map((e) => %s + \" \" + %s).join(\", \") + \"}\"" (apply (with_quotes k) "e[0]")
            (apply (with_quotes v) "e[1]")
      | Some (Types.Record row) ->
          p "(r) => %s(r, { %s })" (native "show-record")
            (String.concat ", " (List.map (fun (k, t) -> p "%s: %s" (key k) (with_quotes t)) (Types.fields row)))
      | Some (Types.Con (k, args) as t) when (match Infer.Env.find_opt k s.state.env.types with Some d -> d.ctors <> [] | None -> false) ->
          constructed k args t
      (* A value of a type nothing fixed is never made: an empty vector's, None's. *)
      | Some (Types.Var _ | Types.Gen _ | Types.Unknown _) -> "String"
      | Some t -> fail ("printing a " ^ Types.show_with (Types.namer ()) t)
      | None -> fail "printing a value of a type the printer does not know"
    and with_quotes t = match t with Types.Con ("String", []) -> native "quote" | t -> show (Some t)
    (* A constructed value: (Some "Ana"), None. *)
    and constructed k args t =
      let id = (names, Types.show_with (Types.namer ()) t) in
      match Hashtbl.find_opt show_helpers id with
      | Some js -> js
      | None ->
          let js = if !compact then fresh () else p "show%s%d" (String.capitalize_ascii (camel (tag k))) (Hashtbl.length show_helpers) in
          Hashtbl.add show_helpers id js;
          let d = Infer.Env.find k s.state.env.types in
          let case (c, fields) =
            let word = js_string (if names then written_as c else tag c) in
            let test = p "if (v.tag === %s) return " (js_string (tag c)) in
            match fields with
            | [] -> test ^ word ^ ";"
            | _ ->
                let each = List.mapi (fun i t -> apply (with_quotes (given args t)) (p "v[%d]" i)) fields in
                p "%s\"(\" + %s + \" \" + %s + \")\";" test word (String.concat " + \" \" + " each)
          in
          (* Printed with the program, which reaches the runtime through vastra. *)
          let inside = !mine in
          mine := true;
          (* Made before it is added: making it can add the helpers it calls. *)
          let code = p "function %s(v) {\n%s\n}" js (block (List.map case d.ctors)) in
          helper_code := code :: !helper_code;
          mine := inside;
          js
    in
    apply (show t) code
  (* A global as a value: a native comes from the runtime. *)
  and value_of n =
    match List.find_opt (fun (top, _, _) -> match top with Native { name; _ } -> name.name = n | _ -> false) entries with
    | Some _ -> native n
    | None -> global n
  (* [e] as statements; its value goes to [ret]. In a task, [e] is a task,
     run, and its result goes to [ret]. *)
  and stmts ?(task = false) ?(back = false) ?tail ?scalar env (e : expr) ret =
    let more = stmts ~task ~back ?tail ?scalar in
    let goes_back (e : expr) = back && List.exists (may_bounce env) (last_calls e) in
    let looping = match tail with Some (self, _) -> tail_calls self e | None -> false in
    match e.kind with
    | Let { bindings; body; how } ->
        let rec go env lines = function
          | [] -> lines @ more env body ret
          | ((b : binding), (v : expr)) :: later -> (
              match (v.kind, how) with
              | Fn l, Recursive ->
                  let env, js = bind env b.name in
                  go env (lines @ [ function_ ~env ~self:b.name js l ~task:false ]) later
              | _ when b.name = "_" -> go env (lines @ [ fst (expr env v) ^ ";" ]) later
              | _ when (match buffer_chain v with Some ({ kind = Var base; _ }, _) -> base = b.name && List.mem_assoc base env | _ -> false) ->
                  let q = List.assoc b.name env in
                  go env (lines @ writes_into env q (snd (Option.get (buffer_chain v)))) later
              | _ when inlinable env v ->
                  let env, ls = inline_into env b.name v (Some (List.map snd later @ [ body ])) in
                  go env (lines @ ls) later
              | Record fs, _
                when List.for_all
                       (fun e -> (not (rebinds b.name e)) && fields_only b.name (List.map fst fs) e)
                       (List.map snd later @ [ body ]) ->
                  let values = List.map (fun (k, v) -> (k, fst (expr env v))) fs in
                  let env, vars = fields env b.name (List.map fst fs) in
                  go env (lines @ List.map (fun (k, js) -> p "const %s = %s;" js (List.assoc k values)) vars) later
              | (If _ | Match _), _ when (not task) && not (one_expression env v) ->
                  let env, ls = branch_into env b.name v (List.map snd later @ [ body ]) in
                  go env (lines @ ls) later
              | _ ->
                  let code = fst (expr env v) in
                  let env, js = bind env b.name in
                  go env (lines @ [ p "const %s = %s;" js code ]) later)
        in
        go env [] bindings
    | Par_let { bindings; body } -> more env { e with kind = Let { bindings; body; how = Names } } ret
    | If { condition; then_branch; else_branch } when task || looping || scalar <> None || inlines env e || not (simple e) || goes_back e ->
        let rec chain (c : expr) t (f : expr) =
          p "if (%s) {\n%s\n}" (fst (expr env c)) (block (more env t ret))
          ^
          match f.kind with
          | If { condition; then_branch; else_branch }
            when task || scalar <> None || inlines env f || not (simple f) || goes_back f
                 || (match tail with Some (self, _) -> tail_calls self f | None -> false) ->
              " else " ^ chain condition then_branch else_branch
          | _ -> p " else {\n%s\n}" (block (more env f ret))
        in
        [ chain condition then_branch else_branch ]
    | Match { scrutinee; clauses } ->
        let lines, it =
          match (scrutinee.kind, e.typed) with
          (* A let's :: decodes its value: (Ok value), or (Err why). *)
          | _, Decodes s ->
              let _, js = bind env "value" in
              ([ p "const %s = %s(%s, %s);" js (native "decoded") (shape_js s) (fst (expr env scrutinee)) ], js)
          | Var n, _ when List.mem_assoc n env -> ([], List.assoc n env)
          | _ -> let _, js = bind env "value" in ([ p "const %s = %s;" js (fst (expr env scrutinee)) ], js)
        in
        (* The checker proved the clauses cover every case: the last needs no
           test. A clause that does not leave has the rest after else. *)
        let rec from = function
          | [] -> []
          | (pat, body) :: rest ->
              let tests, names = pattern it pat in
              let env, binds = List.fold_left (fun (env, ls) (n, access) -> let env, js = bind env n in (env, ls @ [ p "const %s = %s;" js access ])) (env, []) names in
              let inner = binds @ more env body ret in
              if rest = [] || tests = [] then inner
              else
                let test = p "if (%s) {\n%s\n}" (String.concat " && " tests) (block inner) in
                if leaves inner then test :: from rest else [ test ^ p " else {\n%s\n}" (block (from rest)) ]
        in
        lines @ from clauses
    | Call { func = { kind = Var "task/and-then"; _ }; args = [ t; { kind = Fn { params = [ x ]; body = { kind = Call { func = { kind = Var "task/succeed"; _ }; args = [ { kind = Var y; _ } ] }; _ } }; _ } ] }
      when task && x.name = y ->
        more env t ret
    | Call { func = { kind = Var "task/and-then"; _ }; args = [ t; { kind = Fn { params = [ x ]; body }; _ } ] } when task ->
        let code = run env t in
        let env, js = bind env x.name in
        p "const %s = %s;" js code :: more env body ret
    | Call { func = { kind = Var "task/succeed"; _ }; args = [ v ] } when task -> ret (fst (expr env v))
    | Task_of x when task -> more env x ret
    | Set { target = { kind = Var _; _ } as target; path = [ At _ ] as path; value }
      when buffer_chain e = None && is_buffer (type_of target) && not (brief (fst (expr env value))) ->
        let env, js = bind env "#value" in
        p "const %s = %s;" js (fst (expr env value))
        :: more env { e with kind = Set { target; path; value = { value with kind = Var "#value" } } } ret
    | Change _ -> (fst (expr env e) ^ ";") :: ret "undefined"
    | Call { func = { kind = Var n; _ }; args }
      when (match tail with Some (self, params) -> n = self && List.length args = List.length params | None -> false)
           && not (List.mem_assoc n env) ->
        again env args (snd (Option.get tail))
    | Record fs when scalar <> None ->
        let vars, label = Option.get scalar in
        List.map (fun (k, v) -> p "%s = %s;" (List.assoc k vars) (fst (expr env v))) fs
        @ Option.fold label ~none:[] ~some:(fun l -> [ p "break %s;" l ])
    | Call { func = { kind = Var f; _ }; _ } when (not task) && inlinable env e ->
        loop env e (fun v -> let ls = ret v in if leaves ls then ls else ls @ [ p "break %s;" (def_name f) ])
    | Call _ when back && not task ->
        tail_call := true;
        ret (fst (expr env e))
    | _ when task -> ret (run env e)
    | _ -> ret (fst (expr env e))
  (* Whether statements [ls] end by leaving: the last one's first word is
     return, break or continue, so returned = x; doesn't. *)
  and leaves ls =
    match List.rev ls with
    | l :: _ -> (match tokens l with ("return" | "break" | "continue") :: _ -> true | _ -> false)
    | [] -> false
  (* Loop [call], printed here: its result in [x], or in its fields when the
     code after, [rest], reads only them. *)
  and inline_into env x (call : expr) rest =
    let f = match call.kind with Call { func = { kind = Var f; _ }; _ } -> f | _ -> assert false in
    let l = Hashtbl.find loops f in
    match (rest, record_keys (exits f l.body)) with
    | Some rest, Some keys when List.for_all (fun e -> (not (rebinds x e)) && fields_only x keys e) rest ->
        let env', vars = fields env x keys in
        (env', p "let %s;" (String.concat ", " (List.map snd vars)) :: loop env call ~scalar:(vars, Some (def_name f)) (fun _ -> fail "a loop's record"))
    | _ ->
        let env', js = bind env x in
        (env', p "let %s;" js :: loop env call (fun v -> [ p "%s = %s;" js v; p "break %s;" (def_name f) ]))
  (* [v], a value that branches, as statements: its result in [x], or in its
     fields when the code after, [rest], reads only them. *)
  and branch_into env x (v : expr) rest =
    match record_keys (exits "" v) with
    | Some keys when List.for_all (fun e -> (not (rebinds x e)) && fields_only x keys e) rest ->
        let env', vars = fields env x keys in
        (env', p "let %s;" (String.concat ", " (List.map snd vars)) :: stmts ~scalar:(vars, None) env v (fun _ -> fail "a branch's map"))
    | _ ->
        let env', js = bind env x in
        (env', p "let %s;" js :: stmts env v (fun r -> [ p "%s = %s;" js r ]))
  (* A variable for each of [keys] of [x], which is then those variables. *)
  and fields env x keys =
    let env, vars = List.fold_left (fun (env, vs) k -> let env, js = bind env (x ^ "-" ^ k) in (env, vs @ [ (k, js) ])) (env, []) keys in
    let env, js = bind env x in
    Hashtbl.replace scalars js vars;
    (env, vars)
  (* Loop [f] where it is called with [args]. An argument that is a name the
     loop never changes is used as it is; the others start its variables. *)
  and loop env (call : expr) ?scalar ret =
    let func, f, args = match call.kind with Call { func = { kind = Var f; _ } as func; args } -> (func, f, args) | _ -> assert false in
    let l = Hashtbl.find loops f in
    let calls = self_args f l.body in
    let kept i (b : binding) =
      (not (rebinds b.name l.body)) && List.for_all (fun xs -> match (List.nth xs i : expr).kind with Var n -> n = b.name | _ -> false) calls
    in
    let inner, starts =
      List.fold_left
        (fun (inner, starts) (i, ((b : binding), (a : expr))) ->
          let v = fst (expr env a) in
          match a.kind with
          | Var n when List.mem_assoc n env && kept i b -> ((b.name, v) :: inner, starts)
          | _ -> let inner, js = bind inner b.name in (inner, starts @ [ p "%s = %s" js v ]))
        ([], []) (List.mapi (fun i x -> (i, x)) (List.combine l.params args))
    in
    let params = List.map (fun (b : binding) -> List.assoc b.name inner) l.params in
    (* A generic loop is printed for the types of this call. *)
    let saved = !copying in
    if Hashtbl.mem generics f || Hashtbl.mem poly f then copying := subst_for f func (Some args);
    let printed =
      versioned f l params inner (fun () ->
          p "%s: for (;;) {\n%s\n}" (def_name f) (block (stmts ~tail:(f, params) ?scalar inner l.body ret)))
    in
    copying := saved;
    (match starts with
    | [] -> []
    | _ when String.length (String.concat ", " starts) <= 72 -> [ p "let %s;" (String.concat ", " starts) ]
    | _ -> List.map (p "let %s;") starts)
    @ [ printed ]
  (* Loop [self], as [print] writes it, twice when [guards] finds buffers it
     writes into at known indices: once without a test at each write, for when
     they are long enough, as one test before finds. *)
  and versioned self (l : lambda) params env print =
    let rec loops_inside (e : expr) =
      (inlinable env e && match e.kind with Call { func = { kind = Var g; _ }; _ } -> g <> self | _ -> true)
      || List.exists loops_inside (Ast.children e)
    in
    match if loops_inside l.body then [] else guards self l params with
    | [] -> print ()
    | checks ->
        let names = Hashtbl.copy !taken and saved = !unguarded in
        unguarded := List.map fst checks @ saved;
        let fast = print () in
        unguarded := saved;
        taken := names;
        let test = String.concat " && " (List.map (fun (b, hi) -> p "%s.length > %.0f" b hi) checks) in
        p "if (%s) {\n%s\n} else {\n%s\n}" test (block [ fast ]) (block [ print () ])
  (* A call to itself at the end: its parameters take the new values, and the
     loop goes round again. Each value is computed before any changes. *)
  and again env args params =
    (* A loop as an argument runs first, into a variable named after the parameter. *)
    let lifted, env, args =
      List.fold_left
        (fun (ls, env, acc) ((a : expr), q) ->
          if inlinable env a then
            let env, more = inline_into env ("#" ^ q) a None in
            (ls @ more, env, acc @ [ { a with kind = Var ("#" ^ q) } ])
          else (ls, env, acc @ [ a ]))
        ([], env, []) (List.combine args params)
    in
    lifted @ again_ env args params
  and again_ env args params =
    (* The first argument, writes into buffers its own parameter holds: statements. *)
    let first, args, params =
      match (args, params) with
      | ({ kind = Set _; _ } as a) :: rest, q :: qs -> (
          match buffer_chain a with
          | Some ({ kind = Var v; _ }, steps) when List.assoc_opt v env = Some q -> (writes_into env q steps, rest, qs)
          | None -> (
              match a.kind with
              | Set { target = { kind = Var v; _ }; path = [ At _ ] as path; value } when List.assoc_opt v env = Some q ->
                  (writes_into env q [ (path, value) ], rest, qs)
              | _ -> ([], args, params))
          | _ -> ([], args, params))
      | _ -> ([], args, params)
    in
    first @
    let values = List.map (fun a -> fst (expr env a)) args in
    let changed = List.filter (fun (q, v) -> q <> v) (List.combine params values) in
    (* In an order where no value reads a parameter already changed, directly. *)
    let mentions v q = Str.string_match (Str.regexp (".*\\b" ^ Str.quote q ^ "\\b")) v 0 in
    let direct order =
      let rec ok done_ = function
        | [] -> true
        | (q, v) :: rest -> List.for_all (fun d -> not (mentions v d)) done_ && ok (q :: done_) rest
      in
      ok [] order
    in
    (match changed with
    | [] -> []
    | _ when direct changed -> List.map (fun (q, v) -> p "%s = %s;" q v) changed
    | _ when direct (List.rev changed) -> List.map (fun (q, v) -> p "%s = %s;" q v) (List.rev changed)
    | _ ->
        let next = List.map (fun (q, v) -> (q, snd (bind env (q ^ "-next")), v)) changed in
        p "const %s;" (String.concat ", " (List.map (fun (_, t, v) -> p "%s = %s" t v) next))
        :: List.map (fun (q, t, _) -> p "%s = %s;" q t) next)
    @ [ "continue;" ]
  (* Runs a task: a call to what gives one, or a task value called, yielded
     to the runtime, which runs it. *)
  and run env (e : expr) =
    match e.kind with
    | Task_of x -> run env x
    | Call { func = { kind = Var ("vastra.console/print" as n); _ } as f; args } -> fst (native_call env n f args)
    | Call { func = { kind = Var n; _ } as f; args } when gives_task n && not (List.mem_assoc n env) ->
        "yield " ^ fst (native_call env n f args)
    | _ -> p "yield %s()" (paren call (expr env e))
  and function_ ~env ?(task = false) ?self js (l : lambda) =
    in_function (fun () ->
        let env, params = List.fold_left (fun (env, ps) (b : binding) -> let env, js = bind env b.name in (env, ps @ [ js ])) (env, []) l.params in
        let body =
          match self with
          (* JavaScript has no tail calls: a function that calls itself at the end
             is a loop, so it never runs out of stack where Vastra does not. *)
          | Some n when (not task) && tail_calls n l.body ->
              (* A closure made in one round keeps that round's values. *)
              let env, aliases =
                if not (closes l.body) then (env, [])
                else
                  List.fold_left2
                    (fun (env, ls) (b : binding) q -> let env, a = bind env b.name in (env, ls @ [ p "const %s = %s;" a q ]))
                    (env, []) l.params params
              in
              let loop () = p "for (;;) {\n%s\n}" (block (aliases @ stmts ~back:true ~tail:(n, params) env l.body returns)) in
              block [ versioned n l params env loop ]
          | _ -> block (ending (stmts ~task ~back:(not task) env l.body returns))
        in
        p "function%s %s(%s) {\n%s\n}" (if task then "*" else "") js (String.concat ", " params) body)
  and pattern it (pat : pattern) =
    let sub i ps access =
      List.fold_left (fun (ts, ns) (i, q) -> let t, n = pattern (access i) q in (ts @ t, ns @ n)) ([], []) (List.mapi (fun j q -> (i + j, q)) ps)
    in
    match pat.pat with
    | PWild -> ([], [])
    | PVar n -> ([], [ (n, it) ])
    | PInt n -> ([ p "%s === %s" it (whole n) ], [])
    | PStr s -> ([ p "%s === %s" it (js_string s) ], [])
    | PBool b -> ([ (if b then it else "!" ^ it) ], [])
    | PCtor (n, ps) ->
        let t, ns = sub 0 ps (fun i -> p "%s[%d]" it i) in
        (p "%s.tag === %s" it (js_string (tag n)) :: t, ns)
    | PVector ps ->
        let t, ns = sub 0 ps (fun i -> p "%s[%d]" it i) in
        (p "%s.length === %d" it (List.length ps) :: t, ns)
  in
  let show_value = shown in
  (* A top-level task that can fail: how its failure is told, as vastra run
     tells it, the diagnostic made now with the error's text left out. *)
  let untaken = ref false in
  (* The program waits at its top, or sends: its code is a task the runtime
     runs, so the file also loads as a plain script. Imports stay outside it. *)
  let top_awaits = ref false and import_lines = ref [] in
  let failing (task : expr) span =
    match type_of task with
    | Some (Types.Con ("Task", [ (Types.Con _ | Types.Record _ | Types.Fun _) as err; _ ])) when err <> Types.Con ("Never", []) ->
        untaken := true;
        let text = Diagnostic.render (Diagnostic.untaken span "\000") source path in
        let before, after = match String.split_on_char '\000' text with [ b; a ] -> (b, a) | _ -> (text, "") in
        Some (p "%s(x, %s, (e) => %s, %s)" (native "untake") (js_string before) (show_value ~quoted:true (Some err) "e") (js_string after))
    | _ -> None
  in
  let constructors = ref [] in
  (* Each piece is printed once the copies of generic functions are known. *)
  let pieces = ref [] and made = Hashtbl.create 8 in
  let line s = pieces := (!mine, fun () -> s) :: !pieces in
  List.iter
    (fun (top, outcome, shown) ->
      (* What the program's file wrote, apart from what the library did. *)
      mine := shown;
      (match top with
      | Def { name; value = { kind = Run task; span; _ }; _ } -> (
          top_awaits := true;
          let n = global name.name in
          match failing task (if shown then span else Diagnostic.nowhere) with
          | None ->
              (* A name set! changes is a let. *)
              let kind = if Hashtbl.find_opt how name.name = Some Compile.Cell then "let" else "const" in
              List.iter line (stmts ~task:true [] task (fun v -> [ p "%s %s = %s;" kind n v ]))
          | Some told ->
              line (p "let %s;" n);
              line (p "try {\n%s\n} catch (x) {\n%s\n}" (block (stmts ~task:true [] task (fun v -> [ p "%s = %s;" n v ])))
                      (block [ told ^ ";"; p "%s();" (native "finish-now") ])))
      | Def { name; _ } when not (used name.name) -> ()
      | Def { name; _ } when Hashtbl.mem generics name.name || Hashtbl.mem poly name.name ->
          pieces := (!mine, fun () -> String.concat "\n" (List.rev (Hashtbl.find_all made name.name))) :: !pieces
      | Def { name; value = { kind = Fn l; _ }; _ } when Hashtbl.find_opt how name.name <> Some Compile.Cell ->
          let n = name.name in
          let text = function_ ~env:[] ~task:(gives_task n) ~self:n (if Hashtbl.mem loops n then def_name n else global n) l in
          pieces := (!mine, fun () -> if Hashtbl.mem loops n && not (Hashtbl.mem needed n) then "" else text) :: !pieces
      | Def { name; value; _ } ->
          let kw = if Hashtbl.find_opt how name.name = Some Compile.Cell then "let" else "const" in
          let js = global name.name in
          let code =
            match Hashtbl.find_opt columns name.name with
            | Some array -> p "%s %s = %s.from(%s);" kw js array (fst (expr [] value))
            | None -> p "%s %s = %s;" kw js (fst (expr [] value))
          in
          let n = name.name in
          pieces :=
            ( !mine,
              fun () ->
                match Hashtbl.find_opt hoisted n with
                | Some (made, array) -> p "%s\nconst %s = %s.from(%s);" code made array js
                | None -> code )
            :: !pieces
      | Type { ctors; _ } ->
          List.iter
            (fun (c : Ast.ctor) ->
              let js = if !mine then own_js c.ctor_name else camel (tag c.ctor_name) in
              let t = js_string (tag c.ctor_name) in
              constructors :=
                ( !mine,
                  js,
                  (fun () -> used c.ctor_name || Hashtbl.mem in_shapes c.ctor_name),
                  if c.fields = [] then
                    match c.word with
                    | Some w -> p "const %s = { tag: %s, word: %s };" js t (js_string w)
                    | None -> p "const %s = { tag: %s };" js t
                  else
                    let names = List.mapi (fun i _ -> String.make 1 (Char.chr (97 + i))) c.fields in
                    p "const %s = (%s) => ({ tag: %s, %s });" js (String.concat ", " names) t
                      (String.concat ", " (List.mapi (fun i a -> p "%d: %s" i a) names)) )
                :: !constructors)
            ctors
      | Expr e when shown && show ->
          let ty = match outcome with Session.Evaluated { ty; _ } -> ty | _ -> "" in
          (* A function known by name shows it; any other, #<fn>. *)
          let value =
            match e.kind with
            | _ when String.starts_with ~prefix:"(Task " ty -> js_string "#<task>"
            | Keyword k -> js_string (":" ^ k)
            | Var n when String.starts_with ~prefix:"(->" ty -> js_string ("#<fn " ^ written_as n ^ ">")
            | _ when String.starts_with ~prefix:"(->" ty -> js_string "#<fn>"
            | _ -> show_value ~names:true ~quoted:true (type_of e) (fst (expr [] e))
          in
          line (p "console.log(%s + %s);" value (js_string (" : " ^ ty)))
      | Expr e when shown -> (
          match outcome with
          | Session.Evaluated { ty; _ } when Option.fold (read_type ty) ~none:false ~some:is_task -> (
              top_awaits := true;
              let body = stmts ~task:true [] e (fun v -> [ v ^ ";" ]) in
              match failing e e.span with
              | None -> List.iter line body
              | Some told -> line (p "try {\n%s\n} catch (x) {\n%s\n}" (block body) (block [ told ^ ";" ])))
          (* Run for what it does, a send! or a set!, as vastra run runs it. *)
          | _ -> List.iter line (stmts [] e (fun v -> [ v ^ ";" ])))
      | On { handler; waits; _ } -> (
          match (Ast.handler_pattern handler, Ast.handler_body handler) with
          | Some { pat = PCtor (c, ps); _ }, Some body ->
              let env, params =
                List.fold_left
                  (fun (env, ps) (q : pattern) ->
                    match q.pat with
                    | PVar n -> let env, js = bind env n in (env, ps @ [ js ])
                    | PWild -> (env, ps @ [ "_" ])
                    | _ -> fail "a handler's pattern")
                  ([], []) ps
              in
              line
                (p "%s(%s, %s(%s)%s {\n%s\n});" (native "on") (js_string (tag c)) (if waits then "function* " else "")
                   (String.concat ", " params) (if waits then "" else " =>")
                   (block (ending (stmts ~task:waits env body (fun v -> (if v = "undefined" then [] else [ v ^ ";" ]) @ [ "return;" ])))));
          | _ -> fail "a handler's pattern")
      (* The ES modules the program imports: each one's default export if it
         has one, else the module. *)
      | Ns { name; imports; _ } when !mine ->
          List.iter
            (fun (i : Ast.import) ->
              let js = global (name ^ "/" ^ i.local) in
              let m = if !compact then fresh () else js ^ "Module" in
              import_lines := p "import * as %s from %s;" m (js_string i.spec) :: !import_lines;
              line (p "const %s = \"default\" in %s ? %s.default : %s;" js m m m))
            imports
      | View { place; draw; _ } ->
          let d = fst (expr [] draw) in
          line (p "%s(%s, %s);" (native "view") (fst (expr [] place)) (if bounces [] draw then p "%s(%s)" (native "settled") d else d))
      | _ -> ());
      (* With --show, each form's line, as vastra FILE shows it. *)
      match top with
      | Expr _ -> ()
      | _ when show && shown -> line (p "console.log(%s);" (js_string (Session.outcome_to_string outcome)))
      | _ -> ())
    entries;
  (* Copies of generic functions, as their uses asked for them. *)
  while not (Queue.is_empty wanted) do
    let n, subst, js = Queue.pop wanted in
    let l = match Hashtbl.find_opt generics n with Some (_, l) -> l | None -> snd (Hashtbl.find poly n) in
    copying := subst;
    mine := Hashtbl.mem own n;
    Hashtbl.add made n (function_ ~env:[] ~task:(gives_task n) ~self:n js l);
    copying := []
  done;
  mine := true;
  (* After its last line, the program handles the messages it sent; then it
     ends, and what it started stops with it. *)
  let sends = Hashtbl.mem natives (internal "send") in
  if sends then line (p "%s();" (native "handle-sent"));
  if !untaken then line (p "%s();" (native "finish"));
  List.iter (fun code -> pieces := (true, fun () -> code) :: !pieces) (List.rev !helper_code);
  let part m = String.concat "\n" (List.filter (( <> ) "") (List.rev (List.filter_map (fun (m', f) -> if m' = m then Some (f ()) else None) !pieces))) in
  let code = if !top_awaits || sends then p "%s(function* () {\n%s\n});" (native "main") (block [ part true ]) else part true in
  ( List.rev_map (fun (m, js, used, def) -> (m, js, used (), def)) !constructors, part false, String.concat "\n" (List.rev !import_lines @ [ code ]),
    Hashtbl.fold (fun k () acc -> k :: acc) natives [],
    Hashtbl.fold (fun path js acc -> (path, js) :: acc) exports [],
    vastra )

(* The runtime's functions the program uses, and those they use. *)
let runtime used =
  let named = runtime_chunks () in
  (* A paragraph uses another when its code names it: not in a comment or a string. *)
  let mentions c n = List.mem n (tokens c) in
  let rec close seen = function
    | [] -> seen
    | n :: rest when List.mem n seen -> close seen rest
    | n :: rest -> (
        match List.assoc_opt n named with
        | None -> fail ("native " ^ n)
        | Some c -> close (n :: seen) (rest @ List.filter_map (fun (m, _) -> if m <> n && mentions c m then Some m else None) named))
  in
  let chunks = List.filter_map (fun (n, c) -> if List.mem n (close [] used) then Some c else None) named in
  (String.concat "\n\n" (if !compact then List.map shorten chunks else chunks), fun n -> List.exists (fun c -> mentions c n) chunks)

(* What the program reaches in vastra, by path: { on, html: { element: htmlElement } }. *)
let rec object_ entries =
  let heads = List.sort_uniq compare (List.map (fun (path, _) -> List.hd path) entries) in
  let item k =
    match List.filter (fun (path, _) -> List.hd path = k) entries with
    | [ ([ _ ], js) ] when String.starts_with ~prefix:"get:" js -> p "get %s() { return %s; }" k (String.sub js 4 (String.length js - 4))
    | [ ([ _ ], js) ] -> if js = k then k else p "%s: %s" k js
    | group -> p "%s: %s" k (object_ (List.filter_map (fun (path, js) -> match path with _ :: (_ :: _ as rest) -> Some (rest, js) | _ -> None) group))
  in
  let items = List.map item heads in
  let line = "{ " ^ String.concat ", " items ^ " }" in
  if String.length line <= 72 && not (String.contains line '\n') then line
  else "{\n" ^ String.concat "\n" (indent (List.map (fun i -> i ^ ",") items)) ^ "\n}"

(* The program [source], read from [path], as JavaScript: compact, or laid out
   for a reader. *)
let build ~show ~readable path source =
  compact := not readable;
  let written () =
    let ctors, library, code, natives, exports, vastra = program ~show path source in
    let rt, mentioned = runtime natives in
    (* A constructor is defined when the program or the runtime uses it. *)
    let ctors m = String.concat "\n" (List.filter_map (fun (m', js, used, def) -> if m' = m && (used || mentioned js) then Some def else None) ctors) in
    let section title parts =
      match List.filter (( <> ) "") parts with
      | [] -> ""
      | parts -> "// " ^ title ^ "\n\n" ^ String.concat "\n\n" parts
    in
    let inside =
      List.filter (( <> ) "")
        [ section "Its runtime." [ rt ]; section "Its library, compiled." [ ctors false; library ] ]
    in
    let vastra =
      if exports = [] then ""
      else
        p "// Vastra: the parts this program uses.\n\nconst %s = (() => {\n%s\n})();" vastra
          (block (List.map (fun s -> s ^ "\n") inside @ [ "return " ^ object_ exports ^ ";" ]))
    in
    let all = String.concat "\n\n" (List.filter (( <> ) "") [ vastra; section (Filename.basename path) [ ctors true; code ] ]) in
    (if !compact then compactify all else all) ^ "\n"
  in
  match written () with
  | code -> Ok code
  | exception Refused message -> Error message
  | exception Unsupported what -> Error ("vastra build --js: " ^ what ^ " is not written as JavaScript yet")
