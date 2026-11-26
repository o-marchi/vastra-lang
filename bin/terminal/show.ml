(* Results laid out by their shape, read back from their printed code:
   tables, records and dictionaries between their braces, grids and text, under
   a caption with the type and how many. Hints are colour, so what is copied is
   the same text. [result] gives None for a shape it leaves as printed. *)

open Look
module R = Vastra.Reader

let budget = 10
let len = Vastra.Pretty.length (* in characters *)

(* A line, and how many items it shows, for folding. [code]: the last line
   ends in code, so a closing bracket can follow it. [boxed]: the first line
   opens a bracket, so it can start on its key's line. *)
type line = { cells : cell list; n : int }
type shown = { lines : line list; unit : string; count : int; code : bool; boxed : bool }

let pal () = !Theme.current
let spaces n = text plain (String.make (max 0 n) ' ')
let pad_right cells w = cells @ spaces (w - width cells)
let pad_left cells w = spaces (w - width cells) @ cells
let fit w cells = if width cells > w then cut w cells else cells
let punct s = text (fg (pal ()).punct) s
let faint s = text (fg (Theme.faint ())) s
let muted s = text (fg (Theme.muted ())) s
let line ?(n = 1) cells = { cells; n }

(* The printed one-line code of a value. *)
let rec src (n : R.node) =
  let join sep items = String.concat sep (List.map src items) in
  match n.form with
  | Int i | Hex i -> Z.to_string i
  | Float f -> Vastra.Util.float_to_string f
  | Bool b -> string_of_bool b
  | Str s -> "\"" ^ Vastra.Value.escape s ^ "\""
  | Symbol s -> s
  | Keyword k -> ":" ^ k
  | List items -> "(" ^ join " " items ^ ")"
  | Vector items -> "[" ^ join " " items ^ "]"
  | Map entries ->
      "{"
      ^ String.concat ", " (List.map (fun (k, v) -> src k ^ " " ^ src v) entries)
      ^ "}"

let entries (n : R.node) = match n.form with Map es -> es | _ -> []
let is_number (n : R.node) = match n.form with Int _ | Float _ -> true | _ -> false
let is_str (n : R.node) = match n.form with Str _ -> true | _ -> false
let is_keyword (n : R.node) = match n.form with Keyword _ -> true | _ -> false

let is_record (n : R.node) =
  entries n <> [] && List.for_all (fun (k, _) -> is_keyword k) (entries n)

let variant (n : R.node) =
  match n.form with
  | List [ { form = Symbol (("Some" | "Ok" | "Err") as c); _ }; x ] -> Some (c, x)
  | _ -> None

(* The part of an earlier value at an index or a key. *)
let at_index prev i =
  match prev with
  | Some ({ form = Vector xs; _ } : R.node) -> List.nth_opt xs i
  | _ -> None

let at_key prev k =
  Option.bind prev (fun q ->
      List.assoc_opt (src k) (List.map (fun (k, v) -> (src k, v)) (entries q)))

let same_shape (q : R.node) (n : R.node) =
  match (q.form, n.form) with
  | Vector a, Vector b -> List.length a = List.length b
  | List (h :: a), List (h' :: b) -> src h = src h' && List.length a = List.length b
  | Map a, Map b -> List.map (fun (k, _) -> src k) a = List.map (fun (k, _) -> src k) b
  | _ -> false

(* How many parts of [n] differ from the earlier value [q]. *)
let rec differ (q : R.node) (n : R.node) =
  if src q = src n then 0
  else if not (same_shape q n) then 1
  else
    match (q.form, n.form) with
    | (Vector a | List a), (Vector b | List b) ->
        List.fold_left2 (fun m x y -> m + differ x y) 0 a b
    | Map a, Map b -> List.fold_left2 (fun m (_, x) (_, y) -> m + differ x y) 0 a b
    | _ -> 1

let gold cells = List.map (fun c -> { c with style = Theme.bold (Theme.thread ()) }) cells

(* A long integer's digits alternate shade in threes, from the right. *)
let digits s =
  let n = String.length s and colour = (pal ()).number in
  List.init n (fun i ->
      let dim = n > 4 && s.[i] <> '-' && (n - 1 - i) / 3 mod 2 = 1 in
      { ch = String.make 1 s.[i]; style = fg (if dim then Theme.dim colour else colour) })

(* A value on one line, coloured as code; what differs from [prev] in gold. *)
let rec one ?prev (n : R.node) =
  let p = pal () in
  match prev with
  | Some q when src q = src n -> one n
  | Some q when not (same_shape q n) -> gold (one n)
  | _ -> (
      let part i =
        Option.bind prev (fun (q : R.node) ->
            match q.form with Vector xs | List xs -> List.nth_opt xs i | _ -> None)
      in
      let row items =
        List.concat
          (List.mapi
             (fun i x -> (if i > 0 then spaces 1 else []) @ one ?prev:(part i) x)
             items)
      in
      match n.form with
      | Int i | Hex i -> digits (Z.to_string i)
      | Float _ -> text (fg p.number) (src n)
      | Str _ -> text (fg p.str) (src n)
      | Keyword _ -> text (fg p.keyword) (src n)
      | Symbol "Err" -> text (fg p.error) "Err"
      | Bool _ | Symbol _ -> text (fg p.ink) (src n)
      | Vector items -> punct "[" @ row items @ punct "]"
      | List items -> punct "(" @ row items @ punct ")"
      | Map es ->
          let entry i (k, v) =
            (if i > 0 then punct ", " else [])
            @ one k @ spaces 1
            @ one ?prev:(at_key prev k) v
          in
          punct "{" @ List.concat (List.mapi entry es) @ punct "}")

(* The brackets you'd write: the first line opens them, the contents start one
   column in, and the closing follows the last code, or takes a line of its own
   after a table or text. *)
let enclose o c s =
  let lines =
    List.mapi
      (fun i l -> { l with cells = (if i = 0 then punct o else spaces 1) @ l.cells })
      s.lines
  in
  let lines =
    match List.rev lines with
    | last :: rest when s.code ->
        List.rev ({ last with cells = last.cells @ punct c } :: rest)
    | _ -> lines @ [ line ~n:0 (punct c) ]
  in
  { s with lines; code = true; boxed = true }

(* Cut at a character's boundary, not inside one. *)
let common_prefix = function
  | [] -> ""
  | x :: xs ->
      let n =
        List.fold_left
          (fun n y ->
            let rec go i =
              if i < n && i < String.length y && y.[i] = x.[i] then go (i + 1) else i
            in
            go 0)
          (String.length x) xs
      in
      let rec boundary n =
        if n > 0 && n < String.length x && is_cont x.[n] then boundary (n - 1) else n
      in
      String.sub x 0 (boundary n)

(* A vector of records, or of Results whose Oks hold records: the keys once,
   numbers to the right, each row's index; an Err goes across its row. Rows
   come in [order], each keeping its own index. *)
let table ?prev ?order w items =
  let tags = List.map variant items in
  let results = List.for_all Option.is_some tags in
  let record (x : R.node) =
    match variant x with Some (_, r) when results -> r | _ -> x
  in
  let rows =
    Array.of_list
      (List.map
         (fun x ->
           if is_record (record x) then Some (Array.of_list (entries (record x)))
           else None)
         items)
  in
  let full = List.filter_map Fun.id (Array.to_list rows) in
  let keys = Array.map fst (List.hd full) in
  let nc = Array.length keys and nr = Array.length rows in
  let order = Option.value order ~default:(List.init nr Fun.id) in
  (* The row shown above each one, for repeats. *)
  let before = Array.make nr (-1) in
  List.iteri (fun k i -> if k > 0 then before.(i) <- List.nth order (k - 1)) order;
  let srcs = Array.map (Option.map (Array.map (fun (_, v) -> src v))) rows in
  let column c = List.map (fun r -> r.(c)) full in
  let numeric =
    Array.init nc (fun c -> List.for_all (fun (_, v) -> is_number v) (column c))
  in
  let iw = String.length (string_of_int (nr - 1)) and tw = if results then 4 else 0 in
  let cw =
    Array.init nc (fun c ->
        List.fold_left
          (fun m (_, v) -> max m (len (src v)))
          (len (src keys.(c)))
          (column c))
  in
  let total () = iw + 2 + tw + Array.fold_left ( + ) 0 cw + (2 * (nc - 1)) in
  (* The widest text column gives way first, down to 6. *)
  let rec shrink () =
    let best = ref (-1) in
    Array.iteri
      (fun c x ->
        if (not numeric.(c)) && x > 6 && (!best < 0 || x > cw.(!best)) then best := c)
      cw;
    if total () > w && !best >= 0 then (
      cw.(!best) <- cw.(!best) - 1;
      shrink ())
  in
  shrink ();
  (* What every value in a text column begins with fades. *)
  let dim =
    Array.init nc (fun c ->
        let texts = List.map (fun (_, v) -> src v) (column c) in
        let pre = common_prefix texts in
        if
          List.for_all (fun (_, v) -> is_str v) (column c)
          && String.length pre >= 4
          && List.for_all (fun t -> String.length t > String.length pre) texts
        then String.length pre
        else 0)
  in
  let put c cells =
    let cells = fit cw.(c) cells in
    if numeric.(c) then pad_left cells cw.(c)
    else if c = nc - 1 then cells
    else pad_right cells cw.(c)
  in
  let cell i c (r : (R.node * R.node) array) =
    let v = snd r.(c) and s = (Option.get srcs.(i)).(c) in
    let q =
      at_key
        (Option.map
           (fun q -> match variant q with Some (_, r) when results -> r | _ -> q)
           (at_index prev i))
        keys.(c)
    in
    let above = if before.(i) >= 0 then Option.map (fun a -> a.(c)) srcs.(before.(i)) else None in
    match q with
    | Some q when src q <> s -> one ~prev:q v
    | _ when above = Some s -> faint s
    | _ when dim.(c) > 0 ->
        faint (String.sub s 0 dim.(c))
        @ text (fg (pal ()).str) (String.sub s dim.(c) (String.length s - dim.(c)))
    | _ -> one v
  in
  let cols f =
    List.concat (List.init nc (fun c -> (if c > 0 then spaces 2 else []) @ f c))
  in
  let head =
    spaces (iw + 2 + tw)
    @ cols (fun c -> put c (text (fg (pal ()).keyword) (src keys.(c))))
  in
  let row i =
    let tag =
      match List.nth tags i with
      | Some ("Err", _) when results -> text (Theme.bold (Theme.error ())) "Err "
      | Some (t, _) when results -> muted (t ^ String.make (4 - String.length t) ' ')
      | _ -> []
    in
    let body =
      match (rows.(i), List.nth tags i) with
      | Some r, _ -> cols (fun c -> put c (cell i c r))
      | None, Some (_, e) -> text (fg (Theme.error ())) (src e)
      | None, None -> []
    in
    pad_left (faint (string_of_int i)) iw @ spaces 2 @ tag @ body
  in
  {
    lines = line ~n:0 head :: List.map (fun i -> line (row i)) order;
    unit = "rows";
    count = nr;
    code = false;
    boxed = false;
  }

(* Few rows, many keys: keys down the side, one column per element; what is
   the same in every column fades. *)
let sideways ?prev items =
  let rows = List.map entries items in
  let keys = List.map fst (List.hd rows) in
  let kw = List.fold_left (fun m k -> max m (len (src k))) 0 keys in
  let cw =
    List.map (fun r -> List.fold_left (fun m (_, v) -> max m (len (src v))) 1 r) rows
  in
  let last = List.length rows - 1 in
  let put j cells = if j = last then cells else pad_right cells (List.nth cw j) in
  let head =
    spaces (kw + 2)
    @ List.concat
        (List.mapi
           (fun j _ -> (if j > 0 then spaces 2 else []) @ put j (faint (string_of_int j)))
           rows)
  in
  let row k =
    let vs = List.map (fun r -> snd (List.find (fun (k', _) -> src k' = src k) r)) rows in
    let same = List.for_all (fun v -> src v = src (List.hd vs)) vs in
    pad_right (text (fg (pal ()).keyword) (src k)) kw
    @ spaces 2
    @ List.concat
        (List.mapi
           (fun j v ->
             (if j > 0 then spaces 2 else [])
             @ put j
                 (if same then faint (src v) else one ?prev:(at_key (at_index prev j) k) v))
           vs)
  in
  {
    lines = line ~n:0 head :: List.map (fun k -> line ~n:0 (row k)) keys;
    unit = "rows, side by side";
    count = List.length rows;
    code = false;
    boxed = false;
  }

(* Numbers in a grid, right-aligned; anything else flows. *)
let grid ?prev w items =
  let cells = List.mapi (fun i x -> one ?prev:(at_index prev i) x) items in
  let cw = List.fold_left (fun m c -> max m (width c)) 1 cells in
  let numeric = List.for_all is_number items in
  let rec lines acc cur n = function
    | [] ->
        List.rev (if cur = [] then acc else line ~n (List.concat (List.rev cur)) :: acc)
    | c :: rest ->
        let c = if numeric then pad_left c cw else c in
        let wide = List.fold_left (fun m x -> m + width x) 0 cur + 1 + width c in
        if cur <> [] && wide > w then
          lines (line ~n (List.concat (List.rev cur)) :: acc) [ c ] 1 rest
        else lines acc ((if cur = [] then c else spaces 1 @ c) :: cur) (n + 1) rest
  in
  {
    lines = lines [] [] 0 cells;
    unit = "items";
    count = List.length items;
    code = true;
    boxed = false;
  }

let wrap w s =
  let words = String.split_on_char ' ' s in
  let rec go acc cur = function
    | [] -> List.rev (cur :: acc)
    | x :: rest when cur <> "" && len cur + 1 + len x > w -> go (cur :: acc) x rest
    | x :: rest -> go acc (if cur = "" then x else cur ^ " " ^ x) rest
  in
  go [] "" words

(* Text shows its lines, wrapped at words. *)
let text_block w s =
  let parts = String.split_on_char '\n' s in
  let lines =
    List.concat_map
      (fun l -> List.map (fun t -> line (text (fg (pal ()).str) t)) (wrap w l))
      parts
  in
  match parts with
  | [ _ ] -> { lines; unit = "characters"; count = len s; code = false; boxed = false }
  | _ -> { lines; unit = "lines"; count = List.length parts; code = false; boxed = false }

(* Past the second level (or [outline_from]): only the keys, or how many
   items, faint inside the brackets. [outlined]: some part was. *)
let outline_from = ref 1
let outlined = ref false

let outline (v : R.node) =
  outlined := true;
  let many n what = faint (Printf.sprintf "… %d %s" n what) in
  match v.form with
  | Map es when is_record v ->
      punct "{"
      @ List.concat
          (List.mapi
             (fun i (k, _) ->
               (if i > 0 then punct ", " else [])
               @ text (fg (pal ()).keyword) (src k)
               @ faint " …")
             es)
      @ punct "}"
  | Map es -> punct "{" @ many (List.length es) "entries" @ punct "}"
  | Vector xs -> punct "[" @ many (List.length xs) "items" @ punct "]"
  | _ -> one v

let count_label s =
  if s.count = 0 || s.unit = "" then "" else Printf.sprintf "%d %s" s.count s.unit

(* A dictionary of counts tints each entry as far as its share, behind the text. *)
let tint shares s =
  let bar = 40 and top = List.fold_left max 1 shares in
  let paint l share =
    let n = max 1 (share * bar / top) in
    let cells =
      if width l.cells < n + 1 then l.cells @ spaces (n + 1 - width l.cells) else l.cells
    in
    {
      l with
      cells =
        List.mapi
          (fun i c ->
            if i >= 1 && i <= n && c.style.bg = None then
              { c with style = { c.style with bg = Some (Theme.selected ()) } }
            else c)
          cells;
    }
  in
  { s with lines = List.map2 paint s.lines shares }

let rec view ?prev ~depth w (n : R.node) =
  match n.form with
  | Vector (_ :: _ as xs)
    when List.for_all is_record xs
         || List.for_all (fun x -> variant x <> None) xs
            && List.exists
                 (fun x ->
                   match variant x with Some ("Ok", r) -> is_record r | _ -> false)
                 xs ->
      let wide =
        List.exists (fun l -> width l.cells > w) (table ?prev max_int xs).lines
      in
      if wide && List.length xs <= 3 && List.for_all is_record xs then sideways ?prev xs
      else table ?prev w xs
  | Vector xs when List.for_all (fun x -> width (one x) <= w - 2) xs ->
      enclose "[" "]" (grid ?prev (w - 2) xs)
  | Vector xs ->
      let parts =
        List.mapi
          (fun i x -> view ?prev:(at_index prev i) ~depth:(depth + 1) (w - 1) x)
          xs
      in
      let lines =
        List.concat_map
          (fun s ->
            List.mapi (fun i l -> { l with n = (if i = 0 then 1 else 0) }) s.lines)
          parts
      in
      enclose "[" "]"
        {
          lines;
          unit = "items";
          count = List.length xs;
          code = (List.nth parts (List.length parts - 1)).code;
          boxed = true;
        }
  | Map es when es <> [] -> pairs ?prev ~depth w n es
  | Str s when String.contains s '\n' || len (src n) > w -> text_block w s
  | List [ ({ form = Symbol c; _ } : R.node); x ] when variant n <> None ->
      let lead =
        punct "("
        @ text (fg (if c = "Err" then Theme.error () else Theme.ink ())) (c ^ " ")
      in
      let inner =
        view
          ?prev:
            (Option.bind prev (fun (q : R.node) ->
                 match q.form with List [ _; q ] -> Some q | _ -> None))
          ~depth
          (w - width lead)
          x
      in
      let lines =
        List.mapi
          (fun i l ->
            { l with cells = (if i = 0 then lead else spaces (width lead)) @ l.cells })
          inner.lines
      in
      let lines =
        match List.rev lines with
        | last :: rest when inner.code ->
            List.rev ({ last with cells = last.cells @ punct ")" } :: rest)
        | _ -> lines @ [ line ~n:0 (punct ")") ]
      in
      { inner with lines; code = true; boxed = true }
  | _ ->
      {
        lines = List.map (fun c -> line c) (chunks w (one ?prev n));
        unit = "";
        count = 0;
        code = true;
        boxed = true;
      }

(* One entry per line; what fits stays on its key's line. What doesn't starts
   there too if it opens a bracket, goes under it if it is a table or text, or
   past the second level becomes its outline. *)
and pairs ?prev ~depth w n es =
  let dict = not (is_record n) in
  let key k = if dict then one k else text (fg (pal ()).keyword) (src k) in
  let kw = List.fold_left (fun m (k, _) -> max m (width (key k))) 0 es in
  let numeric = dict && List.for_all (fun (_, v) -> is_number v) es in
  let vw = List.fold_left (fun m (_, v) -> max m (len (src v))) 0 es in
  let ends = ref true in
  let entry (k, v) =
    let q = at_key prev k in
    let s = one ?prev:q v and label = pad_right (key k) kw @ spaces 2 in
    if kw + 2 + width s <= w - 2 then (
      ends := true;
      [ line (label @ if numeric then pad_left s vw else s) ])
    else if depth >= !outline_from then (
      ends := true;
      [ line (label @ fit (w - kw - 4) (outline v)) ])
    else
      let beside = view ?prev:q ~depth:(depth + 1) (w - kw - 3) v in
      if beside.boxed then (
        ends := beside.code;
        List.mapi
          (fun i l ->
            {
              cells = (if i = 0 then label else spaces (kw + 2)) @ l.cells;
              n = (if i = 0 then 1 else 0);
            })
          beside.lines)
      else
        let inner = view ?prev:q ~depth:(depth + 1) (w - 3) v in
        ends := inner.code;
        line (label @ muted (count_label inner))
        :: List.map (fun l -> { cells = spaces 2 @ l.cells; n = 0 }) inner.lines
  in
  let lines = List.concat_map entry es in
  let s =
    enclose "{" "}"
      {
        lines;
        unit = (if dict then "entries" else "");
        count = List.length es;
        code = !ends;
        boxed = true;
      }
  in
  let shares =
    List.map
      (fun (_, v) ->
        match v.R.form with Int i when Z.fits_int i -> Z.to_int i | _ -> -1)
      es
  in
  if
    numeric && List.length lines = List.length es && List.for_all (fun x -> x >= 0) shares
  then tint shares s
  else s

(* A tall result shows its first and last lines, with how many more between. *)
let fold budget s =
  let lines = Array.of_list s.lines in
  let k = Array.length lines in
  if k <= budget then (s.lines, false)
  else
    let head = budget - 4 and tail = 3 in
    let hidden = Array.to_list (Array.sub lines head (k - head - tail)) in
    let more = List.fold_left (fun m l -> m + l.n) 0 hidden in
    let more, unit =
      if more = 0 || s.unit = "" then (List.length hidden, "lines") else (more, s.unit)
    in
    (* Inside brackets, the fold lines up with what it stands for. *)
    let indent =
      match hidden with { cells = { ch = " "; _ } :: _; _ } :: _ -> 1 | _ -> 0
    in
    ( Array.to_list (Array.sub lines 0 head)
      @ [ line ~n:0 (spaces indent @ faint (Printf.sprintf "… %d more %s" more unit)) ]
      @ Array.to_list (Array.sub lines (k - tail) tail),
      true )

(* Bars of the values, least to most; more than 24 are taken in 24 parts, each
   shown by its largest. *)
let bars vs =
  let vs = Array.of_list vs in
  let len = Array.length vs in
  let k = min 24 len in
  let lo = Array.fold_left min infinity vs and hi = Array.fold_left max neg_infinity vs in
  let glyphs = [| "▁"; "▂"; "▃"; "▄"; "▅"; "▆"; "▇"; "█" |] in
  String.concat ""
    (List.init k (fun b ->
         let part =
           Array.sub vs (b * len / k) (max 1 (((b + 1) * len / k) - (b * len / k)))
         in
         let v = Array.fold_left max neg_infinity part in
         glyphs.(if hi = lo then 3
                 else int_of_float (Float.round ((v -. lo) /. (hi -. lo) *. 7.)))))

let number (n : R.node) =
  match n.form with Int i -> Some (Z.to_float i) | Float f -> Some f | _ -> None

(* The type with records inside it shortened to {…}, innermost first, until it
   fits; the outermost record stays. *)
let elide t =
  let len = String.length t in
  let rec go i opens =
    if i >= len then t
    else
      match t.[i] with
      | '{' -> go (i + 1) (i :: opens)
      | '}' -> (
          match opens with
          | a :: rest ->
              let inside = String.sub t (a + 1) (i - a - 1) in
              if inside <> "…" && not (a = 0 && i = len - 1) then
                String.sub t 0 (a + 1) ^ "…" ^ String.sub t i (len - i)
              else go (i + 1) rest
          | [] -> t)
      | _ -> go (i + 1) opens
  in
  go 0 []

let flat s =
  String.concat " "
    (List.filter (( <> ) "")
       (String.split_on_char ' ' (String.map (fun c -> if c = '\n' then ' ' else c) s)))

let caption w ty extra =
  let rec go t =
    if len t + width extra <= w then Some t
    else
      let e = elide t in
      if e = t then None else go e
  in
  Option.map (fun t -> Theme.types t @ extra) (go ty)

(* What follows the type in the caption: how many, then what the shape adds. *)
let extras ?prev (n : R.node) s =
  let label = count_label s in
  let changes = match prev with Some q -> differ q n | None -> 0 in
  (if label = "" then [] else muted (" · " ^ label))
  @ (match n.form with
    | Vector xs when List.length xs >= 8 && List.for_all is_number xs ->
        let vs = List.filter_map number xs in
        let show v = src (List.find (fun x -> number x = Some v) xs) in
        muted " · "
        @ text (fg (Theme.thread ())) (bars vs)
        @ muted
            (Printf.sprintf " %s to %s"
               (show (List.fold_left min infinity vs))
               (show (List.fold_left max neg_infinity vs)))
    | Vector xs when List.for_all (fun x -> variant x <> None) xs ->
        let count c =
          List.length
            (List.filter
               (fun x -> match variant x with Some (t, _) -> t = c | None -> false)
               xs)
        in
        let errs = count "Err" in
        if errs = 0 then []
        else
          muted (Printf.sprintf " · %d Ok, " (count "Ok"))
          @ text (fg (Theme.error ())) (Printf.sprintf "%d Err" errs)
    | _ -> [])
  @
  if changes = 0 then []
  else
    muted " · "
    @ text
        (fg (Theme.thread ()))
        (Printf.sprintf "%d change%s since last time" changes
           (if changes = 1 then "" else "s"))

(* The result's rows, its value read back, and whether ↓ would show more. One
   line when it fits; None for a shape left as printed. *)
let result ?prev ?(budget = budget) ?(deep = 1) ~width:w value ty =
  match R.read_all value with
  | Ok [ n ] ->
      let ty = flat ty and whole = one ?prev n in
      let known =
        match n.form with
        | Vector _ | Map (_ :: _) | Str _ -> true
        | List _ -> variant n <> None
        | _ -> false
      in
      if width whole + 3 + len ty <= w then
        Some ([ whole @ muted " : " @ Theme.types ty ], n, false)
      else if not known then None
      else (
        outlined := false;
        outline_from := deep;
        let s = view ?prev ~depth:0 w n in
        let lines, folded = fold budget s in
        let rows = List.map (fun l -> l.cells) lines in
        let cap = caption w ty (extras ?prev n s) in
        Some (Option.to_list cap @ rows, n, folded || !outlined))
  | _ -> None
