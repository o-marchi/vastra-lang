(* Opening a value: the live area shows a value one level at a time, and
   the input holds the code that reaches what is shown. Above every value is
   the session's definitions. *)

open Look
module R = Vastra.Reader

(* A step into a value: a record's key, a vector's index, a dictionary's key. *)
type step = Key of R.node | At of int | Entry of R.node

type t = {
  mutable base : (string * R.node) option;
      (* the code opened, its value; None: the session *)
  mutable steps : step list; (* from the base, outermost first *)
  mutable sel : int; (* the chosen line *)
  mutable sort : (int * bool) option; (* a table's column, and whether descending *)
  mutable names : (string * string) list; (* the session's definitions, with their types *)
}

let at = { base = None; steps = []; sel = 0; sort = None; names = [] }

(* What [key] wants done that the explorer can't do alone. *)
type action = Moved | Closed | Open_name of string | Up_to_session | Not_mine

let rec children (n : R.node) =
  match n.form with
  | Map es when Show.is_record n -> List.map (fun (k, v) -> (Key k, v)) es
  | Map es -> List.map (fun (k, v) -> (Entry k, v)) es
  | Vector xs -> List.mapi (fun i x -> (At i, x)) xs
  | _ -> ( match Show.variant n with Some (_, x) -> children x | None -> [])

let same a b =
  match (a, b) with
  | Key x, Key y | Entry x, Entry y -> Show.src x = Show.src y
  | At i, At j -> i = j
  | _ -> false

let rec node_at n = function
  | [] -> n
  | s :: rest -> (
      match List.find_opt (fun (s', _) -> same s s') (children n) with
      | Some (_, v) -> node_at v rest
      | None -> n)

let current () = Option.map (fun (_, v) -> node_at v at.steps) at.base

let parent () =
  Option.map
    (fun (_, v) ->
      node_at v (List.filteri (fun i _ -> i < List.length at.steps - 1) at.steps))
    at.base

let is_table (n : R.node) =
  match n.form with Vector (_ :: _ as xs) -> List.for_all Show.is_record xs | _ -> false

let keys (n : R.node) =
  match n.form with Vector (x :: _) -> List.map fst (Show.entries x) | _ -> []

let step_code = function Key k | Entry k -> Show.src k | At i -> string_of_int i

(* A table's rows in the order shown, each with its own index. *)
let order (n : R.node) =
  let rows =
    match n.form with Vector xs -> List.mapi (fun i x -> (i, x)) xs | _ -> []
  in
  match at.sort with
  | None -> List.map fst rows
  | Some (c, desc) ->
      let value (_, x) = Show.src (snd (List.nth (Show.entries x) c)) in
      let numeric (_, x) = Show.number (snd (List.nth (Show.entries x) c)) in
      let compare a b =
        match (numeric a, numeric b) with
        | Some x, Some y -> Float.compare x y
        | _ -> String.compare (value a) (value b)
      in
      List.map fst
        (List.stable_sort (fun a b -> if desc then compare b a else compare a b) rows)

(* The code for what is shown. *)
let code () =
  match at.base with
  | None -> ":dir"
  | Some (c, _) -> (
      let c =
        if at.steps = [] then c
        else "(get " ^ c ^ " " ^ String.concat " " (List.map step_code at.steps) ^ ")"
      in
      match (at.sort, current ()) with
      | Some (col, desc), Some n ->
          Printf.sprintf "(sort-by %s %s %s)"
            (Show.src (List.nth (keys n) col))
            (if desc then ">" else "<")
            c
      | _ -> c)

let opening ?(steps = []) base =
  at.base <- base;
  at.steps <- steps;
  at.sel <- 0;
  at.sort <- None

(* How many lines can be chosen where we are. *)
let choices () =
  match current () with
  | None -> List.length at.names
  | Some n -> List.length (children n)

let key (k : Term.key) =
  let n = current () in
  match k with
  | Up ->
      at.sel <- max 0 (at.sel - 1);
      Moved
  | Down ->
      at.sel <- max 0 (min (choices () - 1) (at.sel + 1));
      Moved
  | Right | Enter -> (
      match n with
      | None -> (
          match List.nth_opt at.names at.sel with
          | Some (name, _) -> Open_name name
          | None -> Moved)
      | Some n -> (
          let shown =
            if is_table n then List.nth_opt (order n) at.sel |> Option.map (fun i -> At i)
            else Option.map fst (List.nth_opt (children n) at.sel)
          in
          match shown with
          | Some s ->
              at.steps <- at.steps @ [ s ];
              at.sel <- 0;
              at.sort <- None;
              Moved
          | None -> Moved))
  | Left | Backspace -> (
      match (List.rev at.steps, parent ()) with
      | last :: rest, Some p ->
          at.steps <- List.rev rest;
          at.sort <- None;
          at.sel <-
            Option.value ~default:0
              (List.find_index (fun (s, _) -> same s last) (children p));
          Moved
      | _ -> if at.base = None then Moved else Up_to_session)
  | Char (("[" | "]") as c) -> (
      match (List.rev at.steps, parent ()) with
      | last :: rest, Some p ->
          let kin = children p in
          let i =
            Option.value ~default:0 (List.find_index (fun (s, _) -> same s last) kin)
          in
          let j = max 0 (min (List.length kin - 1) (if c = "[" then i - 1 else i + 1)) in
          at.steps <- List.rev (fst (List.nth kin j) :: rest);
          Moved
      | _ -> Moved)
  | Char d when String.length d = 1 && d.[0] >= '1' && d.[0] <= '9' -> (
      match n with
      | Some n when is_table n && Char.code d.[0] - 49 < List.length (keys n) ->
          let c = Char.code d.[0] - 49 in
          at.sort <-
            (match at.sort with
            | Some (c', false) when c' = c -> Some (c, true)
            | Some (c', true) when c' = c -> None
            | _ -> Some (c, false));
          Moved
      | _ -> Moved)
  | Esc -> Closed
  | _ -> Not_mine

(* A type shortened to fit: records inside it first, as in a caption. *)
let rec shorten room t =
  if Show.len t <= room then t
  else
    let e = Show.elide t in
    if e <> t then shorten room e else if t.[0] = '{' then "{…}" else t

let chosen i row =
  if i = at.sel then
    Area.under (Theme.selected ()) (text (fg (Theme.thread ())) " › " @ row)
  else Area.indent @ row

(* A record among others is named by its text field that differs most between
   them: requests by their path. *)
let telling (kin : (step * R.node) list) =
  let records = List.map snd kin in
  match records with
  | r :: _ when List.for_all Show.is_record records ->
      let fields = List.mapi (fun c (_, v) -> (c, v)) (Show.entries r) in
      let distinct c =
        List.length
          (List.sort_uniq compare
             (List.map (fun x -> Show.src (snd (List.nth (Show.entries x) c))) records))
      in
      let text c =
        List.for_all
          (fun x ->
            let v = snd (List.nth (Show.entries x) c) in
            (not (Show.is_number v)) && Show.len (Show.src v) <= 18)
          records
      in
      List.fold_left
        (fun best (c, _) ->
          if text c && (best = None || distinct c > distinct (Option.get best)) then
            Some c
          else best)
        None fields
  | _ -> None

let label field (s, v) =
  let f = Theme.faint () in
  match (s, field) with
  | At i, Some c ->
      text (fg f) (string_of_int i ^ "  ")
      @ Show.fit 18 (Show.one (snd (List.nth (Show.entries v) c)))
  | At i, None -> text (fg f) (string_of_int i ^ "  ") @ Show.fit 18 (Show.one v)
  | (Key k | Entry k), _ -> Show.one k

(* The rows above the input: where we are, then what is there. *)
let rows ~width ~height =
  let w = width - 1 and room = max 4 (height - 10) in
  let crumbs =
    "session"
    :: (match at.base with Some (c, _) -> c :: List.map step_code at.steps | None -> [])
  in
  let path =
    List.concat
      (List.mapi
         (fun i c ->
           (if i > 0 then text (fg (Theme.faint ())) " › " else [])
           @ text
               (if i = List.length crumbs - 1 then Theme.bold (Theme.ink ())
                else fg (Theme.muted ()))
               c)
         crumbs)
  in
  let body =
    match current () with
    | None ->
        let nw = List.fold_left (fun m (n, _) -> max m (Show.len n)) 0 at.names in
        List.mapi
          (fun i (n, ty) ->
            chosen i
              (Show.pad_right (text (fg (Theme.ink ())) n) (nw + 2)
              @ Show.fit (w - nw - 6) (Theme.types (shorten (w - nw - 6) ty))))
          at.names
    | Some n when is_table n ->
        let t =
          Show.table ~order:(order n) (w - 3)
            (match n.form with Vector xs -> xs | _ -> [])
        in
        List.mapi
          (fun i l ->
            if i = 0 then Area.indent @ l.Show.cells else chosen (i - 1) l.cells)
          t.lines
    | Some n -> (
        let right =
          match children n with
          | [] -> (
              (* Text that doesn't fit shows its lines; anything else, its code. *)
              match n.form with
              | Str s when String.contains s '\n' || Show.len s > w - 30 ->
                  List.map (fun l -> l.Show.cells) (Show.text_block (w - 30) s).lines
              | _ -> [ Show.one n ])
          | kids ->
              let kw =
                List.fold_left
                  (fun m (s, v) -> max m (Look.width (label None (s, v))))
                  0 kids
              in
              List.mapi
                (fun i (s, v) ->
                  chosen i
                    (Show.pad_right (label None (s, v)) (kw + 2)
                    @ Show.fit (w - kw - 34) (Show.one v)))
                kids
        in
        match (parent (), List.rev at.steps) with
        | Some p, last :: _ ->
            let kin = children p in
            let field = telling kin in
            let left =
              List.map
                (fun (s, v) ->
                  let on = same s last in
                  Show.pad_right
                    ((if on then text (fg (Theme.thread ())) " › " else Area.indent)
                    @
                    if on then
                      List.map
                        (fun c -> { c with style = { c.style with bold = true } })
                        (label field (s, v))
                    else label field (s, v))
                    26)
                kin
            in
            List.init
              (max (List.length left) (List.length right))
              (fun i ->
                (match List.nth_opt left i with Some l -> l | None -> Show.spaces 26)
                @ Show.spaces 2
                @ match List.nth_opt right i with Some r -> r | None -> [])
        | _ -> right)
  in
  (* Only as many rows as fit, keeping the chosen one in view. *)
  let first = max 0 (min (at.sel - (room / 2)) (List.length body - room)) in
  let body = List.filteri (fun i _ -> i >= first && i < first + room) body in
  ((Area.indent @ path) :: [] :: body) @ [ [] ]

let hint () =
  let sorts =
    match current () with
    | Some n when is_table n -> [ Printf.sprintf "1–%d sort" (List.length (keys n)) ]
    | _ -> []
  in
  let others = if at.steps <> [] then [ "[ ] the others" ] else [] in
  text
    (fg (Theme.muted ()))
    (String.concat " · "
       ([ "↑↓ choose"; "→ open"; "← back" ] @ others @ sorts @ [ "esc closes" ]))
