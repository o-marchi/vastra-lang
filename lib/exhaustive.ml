(* Missing and unreachable match clauses, after Maranget, "Warnings for pattern
   matching" (2007). A pattern is a wildcard or a constructor with arguments;
   literals and vector lengths are constructors of types that never run out. *)

type pat = W | C of string * pat list

let rec of_ast (p : Ast.pattern) =
  match p.pat with
  | PWild | PVar _ -> W
  | PInt n -> C (Z.to_string n, [])
  | PStr s -> C ("\"" ^ Value.escape s ^ "\"", [])
  | PBool b -> C (string_of_bool b, [])
  | PCtor (name, args) -> C (name, List.map of_ast args)
  | PVector ps -> C ("[" ^ string_of_int (List.length ps) ^ "]", List.map of_ast ps)

let rec show = function
  | W -> "_"
  | C (k, args) when k.[0] = '[' -> "[" ^ String.concat " " (List.map show args) ^ "]"
  | C (k, []) -> k
  | C (k, args) -> "(" ^ k ^ " " ^ String.concat " " (List.map show args) ^ ")"

let wilds n = List.init n (fun _ -> W)

let rec split n l =
  if n = 0 then ([], l)
  else
    match l with
    | x :: rest ->
        let a, b = split (n - 1) rest in
        (x :: a, b)
    | [] -> ([], [])

let rebuild k n witness =
  let args, rest = split n witness in
  C (k, args) :: rest

let specialize k n rows =
  List.filter_map
    (function
      | C (k', args) :: rest -> if k' = k then Some (args @ rest) else None
      | W :: rest -> Some (wilds n @ rest)
      | [] -> None)
    rows

(* A value matched by [q] but by none of [rows], if one exists. [signature k]
   lists every constructor of k's type, when there are finitely many. *)
let rec useful signature rows q =
  match q with
  | [] -> if rows = [] then Some [] else None
  | C (k, args) :: qs ->
      let n = List.length args in
      Option.map (rebuild k n) (useful signature (specialize k n rows) (args @ qs))
  | W :: qs -> (
      let heads =
        List.sort_uniq compare
          (List.filter_map
             (function C (k, a) :: _ -> Some (k, List.length a) | _ -> None)
             rows)
      in
      let all = match heads with (k, _) :: _ -> signature k | [] -> None in
      match all with
      | Some all when List.for_all (fun c -> List.mem c heads) all ->
          List.find_map
            (fun (k, n) ->
              Option.map (rebuild k n)
                (useful signature (specialize k n rows) (wilds n @ qs)))
            all
      | _ ->
          let default =
            List.filter_map (function W :: rest -> Some rest | _ -> None) rows
          in
          let missing =
            match Option.bind all (List.find_opt (fun c -> not (List.mem c heads))) with
            | Some (k, n) -> C (k, wilds n)
            | None -> W
          in
          Option.map (fun w -> missing :: w) (useful signature default qs))

(* [clauses]: whose patterns these are: a match's, a let's, which take a
   value's failure, or a file's handlers', which take its messages. *)
let check ?(clauses = `Match) signature (patterns : Ast.pattern list) span =
  let why =
    match clauses with
    | `Let -> "let-clauses"
    | `Handlers -> "messages"
    | `Match -> "patterns"
  in
  let fail span message note =
    Diagnostic.fail (Diagnostic.make ~why Type span message |> Diagnostic.note note)
  in
  let rows =
    List.fold_left
      (fun rows (p : Ast.pattern) ->
        let row = [ of_ast p ] in
        if useful signature rows row = None then
          if clauses = `Handlers then
            fail p.pat_span "this on can never run"
              "an on before it already takes every message it would"
          else
            fail p.pat_span "this clause can never match"
              "the clauses before it already match every value it would";
        rows @ [ row ])
      [] patterns
  in
  match (useful signature rows [ W ], clauses) with
  | Some (w :: _), `Let ->
      fail span "this let does not handle every failure"
        ("missing: " ^ show w ^ " (add a clause for it)")
  | Some (w :: _), `Handlers ->
      fail span "the file's handlers don't take every message"
        ("missing: " ^ show w ^ " (add an on for it)")
  | Some (w :: _), `Match ->
      fail span "this match does not handle every case"
        ("missing: " ^ show w ^ " (add a clause for it, or end with a _ clause)")
  | _ -> ()
