(* Records are rows: {:name String | r} is open, {:name String} closed. *)

(* Constraints on type variables, from most to least specific: a whole number
   is a number, a number is comparable, a comparable type is equatable, and an
   equatable one holds no buffer, since a buffer is not equatable. That
   last does not print; it keeps why, for the error. A row may be one that
   gains only keys that may be missing, the tail of a map written out,
   and its keys may have a constraint of their own. A child of html is an
   element of that html, a String, or a vector of children. *)
type constr =
  | Integer
  | Number
  | Comparable
  | Equatable
  | Bufferless of string
  | Optional of constr option
  | Child of t

and t =
  | Var of int
  | Gen of int
  | Con of string * t list
  | Fun of t list * t * t (* the parameters, the result, whether it acts *)
  | Record of t
  | Row_empty
  | Row_extend of string * t * t
  (* A part of a name's type that its uses fix: one unknown for the
     whole session, never generic, named after its state. What fixed it is in
     [Infer.env]. *)
  | Unknown of int * string

(* vars.(i) is the constraint of [Gen i]. [holds]: the literals a number
   variable [Gen i] must hold, as (i, (lowest, highest)). [reads]: the
   parameters a function only reads, of those that may hold a buffer.
   [told]: the variable a native is told by the type written on a let, and
   what it is when none is. *)
type scheme = {
  vars : constr option array;
  ty : t;
  holds : (int * (Z.t * Z.t)) list;
  reads : int list;
  told : (int * t) option;
}

let mono ty = { vars = [||]; ty; holds = []; reads = []; told = None }
let con name = Con (name, [])
let int = con "Int"
let float = con "Float"
let str = con "String"
let bool = con "Bool"
let unit = con "Unit"

(* Whether calling a function changes the file's names, as a last part
   of its type no one writes: [acts] does, [plain] never does, and a variable
   acts when the functions that share it do. *)
let acts = con "acts"
let plain = con "plain"

(* A vector's type says whether it is a buffer, as a last argument no
   one writes: [shared] or [unique]. A path steps into a vector of either
   kind, so code written for vectors works on buffers. *)
let shared = con "shared"
let unique = con "unique"
let vector ?(mode = shared) a = Con ("Vector", [ a; mode ])

(* Of two reasons a type holds no buffer, the one it had: [b]. *)
let rec stronger a b =
  match (a, b) with
  | Optional x, Optional y -> Optional (both x y)
  | Optional x, k | k, Optional x -> Optional (both x (Some k))
  | Bufferless _, Bufferless _ -> b
  | _ -> if a < b then a else b

and both x y =
  match (x, y) with
  | Some x, Some y -> Some (stronger x y)
  | Some k, None | None, Some k -> Some k
  | None, None -> None

(* A generic function is told the types of its number variables: a literal of
   that type needs it at run time. *)
let told = function Some (Integer | Number) -> true | _ -> false

let constr_name = function
  | Integer -> "integer"
  | Number -> "number"
  | Comparable -> "comparable"
  | Equatable -> "equatable"
  | Child _ -> "child"
  | Bufferless _ | Optional _ -> "a"

(* Names variables in order of appearance: a, b, ... for types, r, s, ... for
   rows, number, comparable, ... for constrained ones. One namer per message
   keeps names consistent across the types it shows. *)
type namer = {
  plain : bool; (* in an error: unknown parts are _ *)
  names : (t, string) Hashtbl.t;
  counts : (string, int) Hashtbl.t;
  constr_of : t -> constr option;
  shown : string -> string; (* a type's name as typed where it is shown *)
  mutable given : t list; (* the acting variables of functions given as arguments *)
}

let namer ?(plain = false) ?(constr_of = fun _ -> None) ?(shown = Fun.id) () =
  {
    plain;
    names = Hashtbl.create 8;
    counts = Hashtbl.create 4;
    constr_of;
    shown;
    given = [];
  }

(* Notes the acting variables of the functions [ty] takes, in what [n] shows. *)
let rec takes n ?(given = false) = function
  | Fun (ps, r, e) ->
      if given && not (List.mem e n.given) then n.given <- e :: n.given;
      List.iter (takes n ~given:(not given)) ps;
      takes n ~given r
  | Con (_, ts) -> List.iter (takes n ~given) ts
  | Record r -> takes n ~given r
  | Row_extend (_, t, r) ->
      takes n ~given t;
      takes n ~given r
  | _ -> ()

(* How an arrow shows whether its function acts: ->! acts, -> never
   does, and ->? acts when the function it shares a variable with, one given
   as an argument, does. *)
let arrow n = function
  | Con ("acts", []) -> "->!"
  | (Var _ | Gen _) as e when List.mem e n.given -> "->?"
  | _ -> "->"

(* In an error, a part not known is _, and a number left open is number or
   integer, the literals that make it; what else a constraint allows is said
   in words. *)
let plain_name n v =
  match n.constr_of v with Some Number -> "number" | Some Integer -> "integer" | _ -> "_"

let var_name ?kind n v row =
  match Hashtbl.find_opt n.names v with
  | Some name -> name
  | None when n.plain -> plain_name n v
  | None ->
      let constrained = n.constr_of v in
      (* A word (?log, number) is numbered from its second use; letters run on. *)
      let pool, word =
        match (v, constrained) with
        | _ when kind <> None -> (Option.get kind, true)
        | Unknown (_, state), _ ->
            let i = Option.fold (String.rindex_opt state '/') ~none:0 ~some:succ in
            ("?" ^ String.sub state i (String.length state - i), true)
        | _, (None | Some (Bufferless _ | Optional _)) ->
            ((if row then "rstuvwxyz" else "abcdefghijklmnopq"), false)
        | _, Some k -> (constr_name k, true)
      in
      let i = Option.value (Hashtbl.find_opt n.counts pool) ~default:0 in
      Hashtbl.replace n.counts pool (i + 1);
      let name =
        if word then if i = 0 then pool else pool ^ string_of_int i
        else
          let round = i / String.length pool in
          String.make 1 pool.[i mod String.length pool]
          ^ if round = 0 then "" else string_of_int round
      in
      Hashtbl.replace n.names v name;
      name

(* A type's name and arguments as they are written: a vector's kind left open
   is a variable, vector, for a vector or a buffer. *)
let written n name args =
  match (name, args) with
  | "Vector", [ a; Con ("unique", []) ] -> ("Buffer", [ a ])
  | "Vector", [ a; Con _ ] -> ("Vector", [ a ])
  | "Vector", [ a; _ ] when n.plain -> ("Vector", [ a ])
  | "Vector", [ a; kind ] -> (var_name ~kind:"vector" n kind false, [ a ])
  | _ -> (name, args)

(* A map written out shows as written: the keys that may be missing it could
   gain don't show. *)
let open_to_optional n v = match n.constr_of v with Some (Optional _) -> true | _ -> false

(* A row left open: more keys may follow. *)
let row_tail n v = if n.plain then "..." else "| " ^ var_name n v true

let rec doc_with n ty : Pretty.t =
  let group opening items closing = Pretty.Group { opening; items; sep = " "; closing } in
  match ty with
  | (Var _ | Gen _) when n.plain && Hashtbl.find_opt n.names ty = None -> (
      (* A child of html shows as that html. *)
      match n.constr_of ty with
      | Some (Child h) -> doc_with n h
      | _ -> Text (plain_name n ty))
  | Var _ | Gen _ | Unknown _ -> Text (var_name n ty false)
  | Con (name, []) -> Text (n.shown name)
  | Con (name, args) -> (
      (* A vector's type is written like a vector: [Int]. *)
      match written n name args with
      | "Vector", [ a ] -> group "[" [ doc_with n a ] "]"
      | name, args ->
          group ("(" ^ n.shown name ^ " ") (Util.map_in_order (doc_with n) args) ")")
  | Fun (params, ret, e) ->
      let parts = Util.map_in_order (doc_with n) (params @ [ ret ]) in
      group ("(" ^ arrow n e ^ " ") parts ")"
  | Record row | ((Row_empty | Row_extend _) as row) ->
      let rec fields = function
        | Row_extend (key, field, rest) ->
            (* Sequenced: the namer must see the field before the rest of the row. *)
            let field = group (":" ^ key ^ " ") [ doc_with n field ] "" in
            let others, tail = fields rest in
            (field :: others, tail)
        | Row_empty -> ([], "")
        | v when open_to_optional n v -> ([], "")
        | (Var _ | Gen _) as v -> ([], row_tail n v)
        | other -> ([], "| " ^ Pretty.flat (doc_with n other))
      in
      let items, tail = fields row in
      let closing =
        if tail = "" then "}" else if items = [] then tail ^ "}" else " " ^ tail ^ "}"
      in
      Group { opening = "{"; items; sep = ", "; closing }

let show_with n ty =
  takes n ty;
  Pretty.flat (doc_with n ty)

(* A buffer the prompt gives back is shown as a vector. Functions hold
   no buffers, so their types keep them. *)
let rec frozen = function
  | Con ("Vector", [ a; _ ]) -> vector (frozen a)
  | Con (n, args) -> Con (n, List.map frozen args)
  | Record r -> Record (frozen r)
  | Row_extend (k, t, r) -> Row_extend (k, frozen t, frozen r)
  | t -> t

(* A row's keys and their types. *)
let rec fields = function Row_extend (k, t, rest) -> (k, t) :: fields rest | _ -> []

(* Two types with the fields that match written …, to show where they differ:
   each run of matching fields is one …. *)
let rec differ n a b =
  takes n a;
  takes n b;
  let rec tail = function Row_extend (_, _, rest) -> tail rest | t -> t in
  let rec join = function
    | [] -> ""
    | [ x ] -> x
    | "…" :: rest -> "… " ^ join rest
    | x :: rest -> x ^ ", " ^ join rest
  in
  let rec runs = function
    | None :: (None :: _ as rest) -> runs rest
    | None :: rest -> "…" :: runs rest
    | Some x :: rest -> x :: runs rest
    | [] -> []
  in
  let side row theirs =
    let field (k, t) =
      match List.assoc_opt k theirs with
      | Some u when u = t -> None
      | Some u -> Some (":" ^ k ^ " " ^ fst (differ n t u))
      | None -> Some (":" ^ k ^ " " ^ show_with n t)
    in
    let rest =
      match tail row with
      | Row_empty -> ""
      | t when open_to_optional n t -> ""
      | (Var _ | Gen _) as t -> " " ^ row_tail n t
      | t -> " | " ^ show_with n t
    in
    "{" ^ join (runs (List.map field (fields row))) ^ rest ^ "}"
  in
  let call head parts =
    "(" ^ head ^ String.concat "" (List.map (( ^ ) " ") parts) ^ ")"
  in
  match (a, b) with
  | Record ra, Record rb ->
      let a = side ra (fields rb) in
      (a, side rb (fields ra))
  | Con (x, xs), Con (y, ys) when x = y && xs <> [] && List.length xs = List.length ys ->
      let x, xs = written n x xs in
      let y, ys = written n y ys in
      let parts = List.map2 (differ n) xs ys in
      let con x parts =
        if x = "Vector" then "[" ^ String.concat " " parts ^ "]" else call (n.shown x) parts
      in
      (con x (List.map fst parts), con y (List.map snd parts))
  | Fun (ps, r, e), Fun (qs, s, f) when List.length ps = List.length qs ->
      let parts = List.map2 (differ n) (ps @ [ r ]) (qs @ [ s ]) in
      (call (arrow n e) (List.map fst parts), call (arrow n f) (List.map snd parts))
  | _ ->
      let a = show_with n a in
      (a, show_with n b)

let show_scheme ?plain ?shown ?width ?col (s : scheme) =
  let constr_of = function
    | Gen i when i < Array.length s.vars -> s.vars.(i)
    | _ -> None
  in
  let n = namer ?plain ~constr_of ?shown () in
  takes n s.ty;
  (* A parameter the function only reads is marked &. *)
  let doc =
    match s.ty with
    | Fun (params, ret, e) when s.reads <> [] ->
        let param (i, p) =
          let doc = doc_with n p in
          if not (List.mem i s.reads) then doc
          else Pretty.Group { opening = "&"; items = [ doc ]; sep = ""; closing = "" }
        in
        let params = Util.map_in_order param (List.mapi (fun i p -> (i, p)) params) in
        let items = params @ [ doc_with n ret ] in
        Pretty.Group { opening = "(" ^ arrow n e ^ " "; items; sep = " "; closing = ")" }
    | ty -> doc_with n ty
  in
  Pretty.render ?width ?col doc

(* The same type, as a redefinition keeps it. The fixed-width types a
   function's literals rule out are part of it, though they do not print, as
   are the variables that hold no buffer and the maps written out. *)
let same a b =
  (* The variables' constraints, without why one holds no buffer. *)
  let rec unsaid = function
    | Bufferless _ -> Bufferless ""
    | Optional k -> Optional (Option.map unsaid k)
    | k -> k
  in
  let constraints s = Array.map (Option.map unsaid) s.vars in
  let ruled_out s =
    List.filter_map
      (fun (g, (lo, hi)) ->
        let out (f : Num.fixed) =
          let min, max = Num.range f in
          Z.lt lo min || Z.gt hi max
        in
        match List.filter out Num.fixed with [] -> None | fs -> Some (g, fs))
      s.holds
  in
  (* Two names' unknowns print alike. *)
  let rec unknowns = function
    | Unknown (u, _) -> [ u ]
    | Con (_, ts) -> List.concat_map unknowns ts
    | Fun (ps, r, _) -> List.concat_map unknowns (r :: ps)
    | Record r -> unknowns r
    | Row_extend (_, t, r) -> unknowns t @ unknowns r
    | _ -> []
  in
  show_scheme a = show_scheme b
  && ruled_out a = ruled_out b
  && constraints a = constraints b
  && unknowns a.ty = unknowns b.ty
