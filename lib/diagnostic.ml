(* [Command]: the code is fine, and the command that ran it doesn't do what it
   needs. *)
type phase = Read | Syntax | Name | Type | Runtime | Command

(* The fix an error gives as code: its span's text corrected, shown in
   its line, or what to run instead. An edit that can't find what it corrects
   gives None, and the error no fix. *)
type fix = Edit of Reader.span * (string -> string option) | Run of string

(* [file] (origin, source) is set when the error is in another file than the one being run. *)
type t = {
  phase : phase;
  message : string;
  span : Reader.span;
  caption : string; (* what the span is, after its carets *)
  marks : (Reader.span * string) list; (* other places, underlined more quietly *)
  notes : string list;
  fix : fix option;
  why : string; (* the rule's key in why.txt, for :why; "" if none yet *)
  file : (string * string) option;
  against : (string * int) option; (* a name, its unknown whose fixing this disputes *)
}

exception Error of t

(* The span of an error with no place in the code. *)
let nowhere = { Reader.start = -1; stop = -1 }

let make ?(why = "") phase span message =
  {
    phase;
    message;
    span;
    caption = "";
    marks = [];
    notes = [];
    fix = None;
    why;
    file = None;
    against = None;
  }

let note text d = { d with notes = d.notes @ [ text ] }
let caption text d = { d with caption = text }
let mark span text d = { d with marks = d.marks @ [ (span, text) ] }
let fix f d = { d with fix = Some f }
let why key d = { d with why = key }

(* An error that is Vastra's own bug, wherever it is caught. *)
let bug span message =
  make ~why:"bug" Runtime span ("internal error: " ^ message)
  |> note "this is a bug in Vastra, not in the program"

(* A top-level task that failed: the same error from vastra run, the REPL's
   definitions and a built program. *)
let untaken span error =
  make ~why:"task-failed" Runtime span
    (Printf.sprintf "this task failed with %s, and nothing takes the failure" error)
  |> note "a let's clause takes it: (let text @(file/read-text path) [(Err why) ...])"
let fail d = raise (Error d)

let label = function
  | Read -> "read error"
  | Syntax -> "syntax error"
  | Name -> "name error"
  | Type -> "type error"
  | Runtime -> "runtime error"
  | Command -> "command error"

let is_continuation c = Char.code c land 0xC0 = 0x80

let char_count s a b =
  let n = ref 0 in
  for i = a to b - 1 do
    if not (is_continuation s.[i]) then incr n
  done;
  !n

(* The line, counted from 1, of byte [i] of [source]. *)
let line source i = List.length (String.split_on_char '\n' (String.sub source 0 i))

let floor_boundary s i =
  let i = ref (min i (String.length s)) in
  while !i > 0 && !i < String.length s && is_continuation s.[!i] do
    decr i
  done;
  !i

(* The line of byte [i]: its number, and the bytes it starts and ends at. *)
let line_of source i =
  let start =
    match String.rindex_from_opt source (i - 1) '\n' with Some j -> j + 1 | None -> 0
  in
  let stop =
    Option.value (String.index_from_opt source i '\n') ~default:(String.length source)
  in
  (line source i, start, stop)

(* What a span underlines with [mark]: its first line and, if it goes on, its
   last, as (line, line start, line end, from, to, mark, label), in bytes. The
   label goes on the last. *)
let pieces source (span : Reader.span) mark label =
  let start = floor_boundary source span.start in
  let first, a, b = line_of source start in
  let stop = ref (floor_boundary source (max start span.stop)) in
  (* A string never closed runs to the end, past lines that show nothing. *)
  while !stop > start + 1 && String.contains " \t\r\n" source.[!stop - 1] do
    decr stop
  done;
  let stop = !stop in
  let last, c, e = line_of source (floor_boundary source (max start (stop - 1))) in
  if first = last then [ (first, a, b, start, min stop b, mark, label) ]
  else
    let indent = ref c in
    while !indent < stop && (source.[!indent] = ' ' || source.[!indent] = '\t') do
      incr indent
    done;
    [ (first, a, b, start, b, mark, ""); (last, c, e, !indent, stop, mark, label) ]

(* The lines of [fix] applied, without their common indent. *)
let fixed source = function
  | Run command -> [ command ]
  | Edit (span, f) -> (
      let _, a, _ = line_of source span.start in
      let _, _, b = line_of source (max span.start (span.stop - 1)) in
      match f (String.sub source span.start (span.stop - span.start)) with
      | None -> []
      | Some corrected ->
          let text =
            String.sub source a (span.start - a)
            ^ corrected
            ^ String.sub source span.stop (b - span.stop)
          in
          let lines = String.split_on_char '\n' text in
          let indent l =
            let n = ref 0 in
            while !n < String.length l && l.[!n] = ' ' do
              incr n
            done;
            !n
          in
          let cut = indent (List.hd lines) in
          List.map
            (fun l ->
              let n = min cut (indent l) in
              String.sub l n (String.length l - n))
            lines)

(* [text] with the first [old] that is not part of a longer name written
   [updated]. *)
let replace_word old updated text =
  let n = String.length old and len = String.length text in
  let apart i = i < 0 || i >= len || String.contains " \t\n,()[]{}" text.[i] in
  let rec at i =
    if i + n > len then None
    else if String.sub text i n = old && apart (i - 1) && apart (i + n) then
      Some (String.sub text 0 i ^ updated ^ String.sub text (i + n) (len - i - n))
    else at (i + 1)
  in
  at 0

(* [text] with the name [old] written [updated], or the keyword a macro made
   it from: :clas, which html reads as html/clas. *)
let rename old updated text =
  let last s =
    match String.rindex_opt s '/' with
    | Some i -> ":" ^ String.sub s (i + 1) (String.length s - i - 1)
    | None -> s
  in
  match replace_word old updated text with
  | None when last old <> old -> replace_word (last old) (last updated) text
  | t -> t

let rekey old updated = replace_word (":" ^ old) (":" ^ updated)

(* The try: line of [d], in [source] unless it is in another file. *)
let tried d source =
  let source = match d.file with Some (_, s) -> s | None -> source in
  match Option.map (fixed source) d.fix with
  | Some (first :: rest) -> ("try: " ^ first) :: List.map (( ^ ) "     ") rest
  | _ -> []

(* The lines after the frame: notes, then the fix. *)
let tail d source = List.map (( ^ ) "= ") d.notes @ tried d source

(* type error: message
    --> origin:line:column
     |
   1 | source line
     |   ^^^^ caption
     = note
     try: fixed line
   A long span shows its first and last lines, other places are underlined
   with -, and a gap between lines shown is "...". Source [on_screen] (just
   typed at the prompt) needs no place named, and line numbers only when it
   has several lines. *)
let rec render ?(on_screen = false) d source origin =
  if d.span.start < 0 then
    String.concat "\n  "
      (Printf.sprintf "%s: %s" (label d.phase) d.message :: tail d source)
  else frame ~on_screen d source origin

and frame ~on_screen d source origin =
  let on_screen = on_screen && d.file = None in
  let source, origin =
    match d.file with Some (o, s) -> (s, o) | None -> (source, origin)
  in
  let numbered = not on_screen || String.contains (String.trim source) '\n' in
  let marks =
    pieces source d.span '^' d.caption
    @ List.concat_map (fun (span, text) -> pieces source span '-' text) d.marks
  in
  let lines =
    List.sort_uniq compare (List.map (fun (l, a, b, _, _, _, _) -> (l, a, b)) marks)
  in
  let width =
    if not numbered then 1
    else String.length (string_of_int (List.fold_left (fun m (l, _, _) -> max m l) 0 lines))
  in
  let gutter = String.make width ' ' in
  let row (l, a, b) =
    let col i = char_count source a i in
    let here =
      List.filter (fun (m, _, _, _, _, _, _) -> m = l) marks
      |> List.sort (fun (_, _, _, x, _, _, _) (_, _, _, y, _, _, _) -> compare x y)
    in
    let under = Buffer.create 80 in
    List.iter
      (fun (_, _, _, from, upto, mark, _) ->
        if col from >= Buffer.length under then (
          Buffer.add_string under (String.make (col from - Buffer.length under) ' ');
          let width = max 1 (char_count source from upto) in
          Buffer.add_string under (String.make width mark)))
      here;
    (* The last label follows its marks; the others go below, nearest first. *)
    let labelled = List.rev (List.filter (fun (_, _, _, _, _, _, t) -> t <> "") here) in
    let below =
      match (labelled, List.rev here) with
      | (_, _, _, x, _, _, t) :: rest, (_, _, _, y, _, _, _) :: _ when x = y ->
          Buffer.add_string under (" " ^ t);
          rest
      | _ -> labelled
    in
    let number = if numbered then string_of_int l else "" in
    Printf.sprintf "\n%*s | %s\n%s | %s" width number (String.sub source a (b - a)) gutter
      (Buffer.contents under)
    ^ String.concat ""
        (List.map
           (fun (_, _, _, from, _, _, t) ->
             Printf.sprintf "\n%s | %s%s" gutter (String.make (col from) ' ') t)
           below)
  in
  let rec rows previous = function
    | [] -> ""
    | ((l, _, _) as x) :: rest ->
        (if previous > 0 && l > previous + 1 then "\n..." else "") ^ row x ^ rows l rest
  in
  let start = floor_boundary source d.span.start in
  let line, line_start, _ = line_of source start in
  Printf.sprintf "%s: %s" (label d.phase) d.message
  ^ (if on_screen then ""
     else
       Printf.sprintf "\n%s--> %s:%d:%d\n%s |" gutter origin line
         (char_count source line_start start + 1)
         gutter)
  ^ rows 0 lines
  ^ String.concat "" (List.map (Printf.sprintf "\n%s %s" gutter) (tail d source))

let of_read_error (e : Reader.error) =
  let rule : Reader.error_kind -> string = function
    | Unclosed _ | Mismatched _ | Unexpected_closing _ -> "brackets"
    | Unterminated_string | Invalid_escape _ -> "strings"
    | Invalid_number | Exponent -> "numbers"
    | Odd_map_entries -> "maps"
    | Not_a_reader_form | Nested_short_fn | Parameter_outside _ -> "short-fn"
    | Caret_without_name -> "parallel"
    | No_type -> "written-types"
    | Empty_keyword | Dangling _ -> "reader-marks"
  in
  let d message = why (rule e.kind) (make Read e.span message) in
  match e.kind with
  | Unclosed c -> d (Printf.sprintf "this `%c` is never closed" c)
  | Mismatched { expected; found } ->
      d (Printf.sprintf "expected `%c` but found `%c`" expected found)
  | Unexpected_closing c -> d (Printf.sprintf "unexpected `%c` with nothing to close" c)
  | Unterminated_string -> d "this string is never closed"
  | Invalid_escape c ->
      d (Printf.sprintf "unknown escape `\\%s`" c)
      |> note {|supported escapes are \" \\ \n \t|}
  | Odd_map_entries -> d "a map needs an even number of forms (key/value pairs)"
  | Invalid_number -> d "invalid number" |> note "numbers are written like 42, -7, 1.5 or 0xff"
  | Exponent ->
      d "a number is written without an exponent" |> note "for example: 1500.0, not 1.5e3"
  | Empty_keyword -> d "a `:` must be followed by a name"
  | Dangling mark -> d (Printf.sprintf "`%s` must be followed by a form" mark)
  | Not_a_reader_form ->
      d "`#` must be followed by `(`"
      |> note "the only reader form starting with # is #(...), a small function like #(+ % 1)"
  | Nested_short_fn -> d "`#(...)` inside `#(...)`: write the outer one with `fn`"
  | Parameter_outside name -> d (Printf.sprintf "`%s` is a parameter of `#(...)` only" name)
  | Caret_without_name ->
      d "`^` must be followed by a name" |> note "^map is par/map, as in (^map f xs)"
  | No_type ->
      d "`::` must be followed by a type, with no space"
      |> note "for example: (let seed::U32 1)"

let plural n word = if n = 1 then "1 " ^ word else Printf.sprintf "%d %ss" n word

let uchars s =
  let rec go i acc =
    if i >= String.length s then Array.of_list (List.rev acc)
    else
      let d = String.get_utf_8_uchar s i in
      go (i + Uchar.utf_decode_length d) (Uchar.utf_decode_uchar d :: acc)
  in
  go 0 []

(* Optimal string alignment: an adjacent swap costs 1, so `nmae` is 1 from `name`. *)
let distance a b =
  let a = uchars a and b = uchars b in
  let la = Array.length a and lb = Array.length b in
  let d = Array.make_matrix (la + 1) (lb + 1) 0 in
  for i = 0 to la do
    d.(i).(0) <- i
  done;
  for j = 0 to lb do
    d.(0).(j) <- j
  done;
  for i = 1 to la do
    for j = 1 to lb do
      let cost = if Uchar.equal a.(i - 1) b.(j - 1) then 0 else 1 in
      d.(i).(j) <-
        min (min (d.(i - 1).(j) + 1) (d.(i).(j - 1) + 1)) (d.(i - 1).(j - 1) + cost);
      if
        i > 1 && j > 1
        && Uchar.equal a.(i - 1) b.(j - 2)
        && Uchar.equal a.(i - 2) b.(j - 1)
      then d.(i).(j) <- min d.(i).(j) (d.(i - 2).(j - 2) + 1)
    done
  done;
  d.(la).(lb)

(* The closest plausible typo of [target]. Ties go to the earliest candidate,
   so callers list the most relevant names first (locals before globals). The
   limit counts only what follows a module, so string/ doesn't widen it. *)
let suggest target candidates =
  let name =
    match String.rindex_opt target '/' with
    | Some i when i < String.length target - 1 ->
        String.sub target (i + 1) (String.length target - i - 1)
    | _ -> target
  in
  let limit = max 1 (Array.length (uchars name) / 3) in
  (* Every character changed is no typo: x is not a misspelt *. *)
  candidates
  |> List.filter (( <> ) target)
  |> List.map (fun c -> (distance target c, c))
  |> List.filter (fun (d, _) -> d <= limit && d < Array.length (uchars name))
  |> List.stable_sort (fun (a, _) (b, _) -> compare a b)
  |> function
  | (_, best) :: _ -> Some best
  | [] -> None
