(* Text → data. Spans are byte offsets [start, stop) into the source. *)

type span = { start : int; stop : int }

type form =
  | Int of Z.t
  | Hex of Z.t (* written in hex: a whole number, never a Float *)
  | Float of float
  | Bool of bool
  | Str of string
  | Symbol of string
  | Keyword of string
  | List of node list
  | Vector of node list
  | Map of (node * node) list

(* [origin] names the macro that produced a node, for error messages. *)
and node = { form : form; span : span; origin : string option }

type error_kind =
  | Unclosed of char
  | Mismatched of { expected : char; found : char }
  | Unexpected_closing of char
  | Unterminated_string
  | Invalid_escape of string
  | Odd_map_entries
  | Invalid_number
  | Exponent (* 1e3, which Vastra doesn't read *)
  | Empty_keyword
  | Dangling of string
  | Not_a_reader_form
  | Nested_short_fn
  | Parameter_outside of string
  | Caret_without_name
  | No_type (* name:: with no type after it *)

type error = { kind : error_kind; span : span }

exception Read_error of error

let node form span = { form; span; origin = None }
let is c u = Uchar.equal u (Uchar.of_char c)

(* Unicode White_Space. *)
let is_whitespace u =
  match Uchar.to_int u with
  | 0x09 | 0x0A | 0x0B | 0x0C | 0x0D | 0x20 | 0x85 | 0xA0 | 0x1680 | 0x2028 | 0x2029
  | 0x202F | 0x205F | 0x3000 ->
      true
  | c -> c >= 0x2000 && c <= 0x200A

let is_closing u = is ')' u || is ']' u || is '}' u

let is_terminator u =
  is_whitespace u
  || List.exists (fun c -> is c u) [ ','; ';'; '"'; '('; ')'; '['; ']'; '{'; '}' ]

(* [params] are the parameters used so far inside #(...), with the span of
   each one's first use, or None outside it. *)
type state = { source : string; mutable pos : int; mutable params : (int * span) list option }

let decode st = String.get_utf_8_uchar st.source st.pos

let peek st =
  if st.pos >= String.length st.source then None
  else Some (Uchar.utf_decode_uchar (decode st))

let advance st =
  let d = decode st in
  st.pos <- st.pos + Uchar.utf_decode_length d;
  Uchar.utf_decode_uchar d

let span_from st start = { start; stop = st.pos }
let fail kind span = raise (Read_error { kind; span })

let fail_here st kind =
  let len =
    if st.pos >= String.length st.source then 0 else Uchar.utf_decode_length (decode st)
  in
  fail kind { start = st.pos; stop = st.pos + len }

let rec skip_blank st =
  match peek st with
  | Some u when is ';' u ->
      while peek st <> None && not (is '\n' (advance st)) do
        ()
      done;
      skip_blank st
  | Some u when is_whitespace u || is ',' u ->
      ignore (advance st);
      skip_blank st
  | _ -> ()

let is_digit c = c >= '0' && c <= '9'
let is_hex c = is_digit c || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F')

let unsigned t =
  if String.starts_with ~prefix:"-" t then String.sub t 1 (String.length t - 1) else t

(* The number of a parameter of #(...): 1 for `%` and `%1`, 2 for `%2`…
   Other names starting with %, `%0` among them, are ordinary names. *)
let parameter = function
  | "%" -> Some 1
  | t when String.starts_with ~prefix:"%" t ->
      let digits = String.sub t 1 (String.length t - 1) in
      if digits.[0] <> '0' && String.for_all is_digit digits then int_of_string_opt digits
      else None
  | _ -> None

let parameter_name n = "%" ^ string_of_int n

(* Where a name's written type starts: the :: after it, if any. *)
let find_colons token =
  let rec from i =
    if i + 1 >= String.length token then None
    else if token.[i] = ':' && token.[i + 1] = ':' then Some i
    else from (i + 1)
  in
  if String.starts_with ~prefix:":" token then None else from 1

let rec read_form st first =
  if is '(' first then read_collection st '(' ')'
  else if is '[' first then read_collection st '[' ']'
  else if is '{' first then read_collection st '{' '}'
  else if is '"' first then read_string st
  else if is '\'' first then read_prefix st "quote" 1
  else if is '`' first then read_prefix st "quasiquote" 1
  else if is '@' first then read_prefix st "await" 1
  else if is '#' first then read_short_fn st
  else if is '^' first then read_parallel st
  else if is '~' first then
    let splice = st.pos + 1 < String.length st.source && st.source.[st.pos + 1] = '@' in
    if splice then read_prefix st "unquote-splicing" 2 else read_prefix st "unquote" 1
  else read_atom st

(* 'x is (quote x); likewise ` (quasiquote), @ (await), ~ (unquote), ~@
   (unquote-splicing). *)
and read_prefix st name len =
  let start = st.pos in
  let mark = String.sub st.source start len in
  st.pos <- st.pos + len;
  skip_blank st;
  match peek st with
  | Some u when not (is_closing u) ->
      let inner = read_form st u in
      node
        (List [ node (Symbol name) { start; stop = start + len }; inner ])
        (span_from st start)
  | _ -> fail (Dangling mark) { start; stop = start + len }

(* #(...) is a fn whose body is the list: #(+ % 1) is (fn [%1] (+ %1 1)),
   taking as many parameters as the highest one used. *)
and read_short_fn st =
  let start = st.pos in
  ignore (advance st);
  match peek st with
  | Some u when is '(' u ->
      if st.params <> None then fail Nested_short_fn { start; stop = start + 2 };
      st.params <- Some [];
      let body = read_collection st '(' ')' in
      let used = Option.get st.params in
      st.params <- None;
      let span = span_from st start in
      let highest = List.fold_left (fun m (n, _) -> max m n) 0 used in
      let param n =
        node (Symbol (parameter_name n)) (Option.value (List.assoc_opt n used) ~default:span)
      in
      node
        (List
           [
             node (Symbol "fn") { start; stop = start + 1 };
             node (Vector (List.init highest (fun i -> param (i + 1)))) span;
             body;
           ])
        span
  | _ -> fail Not_a_reader_form { start; stop = start + 1 }

(* ^map is the core's par/map, whatever a module calls par: the session
   resolves ^ names to the core's. ^let is the special form par/let itself. *)
and read_parallel st =
  let start = st.pos in
  ignore (advance st);
  let caret = { start; stop = start + 1 } in
  match peek st with
  | Some u when not (is_terminator u) -> (
      match (read_atom st).form with
      | Symbol "let" -> node (Symbol "par/let") (span_from st start)
      | Symbol name -> node (Symbol ("^" ^ name)) (span_from st start)
      | _ -> fail Caret_without_name caret)
  | _ -> fail Caret_without_name caret

and read_collection st opening closing =
  let start = st.pos in
  ignore (advance st);
  let rec items acc =
    skip_blank st;
    match peek st with
    | None -> fail (Unclosed opening) { start; stop = start + 1 }
    | Some u when is closing u ->
        ignore (advance st);
        List.rev acc
    | Some u when is_closing u ->
        fail_here st (Mismatched { expected = closing; found = Uchar.to_char u })
    | Some u -> items (read_form st u :: acc)
  in
  let items = items [] in
  let span = span_from st start in
  let rec pairs = function
    | [] -> []
    | [ _ ] -> fail Odd_map_entries span
    | k :: v :: rest -> (k, v) :: pairs rest
  in
  node
    (match opening with
    | '(' -> List items
    | '[' -> Vector items
    | _ -> Map (pairs items))
    span

and read_string st =
  let start = st.pos in
  ignore (advance st);
  let text = Buffer.create 16 in
  let rec loop () =
    let escape_start = st.pos in
    match peek st with
    | None -> fail Unterminated_string (span_from st start)
    | Some _ -> (
        match advance st with
        | u when is '"' u -> ()
        | u when is '\\' u ->
            (match peek st with
            | None -> fail Unterminated_string (span_from st start)
            | Some _ -> (
                match Uchar.to_int (advance st) with
                | 0x22 -> Buffer.add_char text '"'
                | 0x5C -> Buffer.add_char text '\\'
                | 0x6E -> Buffer.add_char text '\n'
                | 0x74 -> Buffer.add_char text '\t'
                | c ->
                    let b = Buffer.create 4 in
                    Buffer.add_utf_8_uchar b (Uchar.of_int c);
                    fail (Invalid_escape (Buffer.contents b)) (span_from st escape_start)));
            loop ()
        | u ->
            Buffer.add_utf_8_uchar text u;
            loop ())
  in
  loop ();
  node (Str (Buffer.contents text)) (span_from st start)

and read_atom st =
  let start = st.pos in
  while match peek st with Some u -> not (is_terminator u) | None -> false do
    ignore (advance st)
  done;
  let token = String.sub st.source start (st.pos - start) in
  match find_colons token with
  | Some i -> read_written st start token i
  | None -> atom st start token

and atom st start token =
  let span = span_from st start in
  let digits = unsigned token in
  let form =
    if String.starts_with ~prefix:"0x" digits then
      let hex = String.sub digits 2 (String.length digits - 2) in
      if hex <> "" && String.for_all is_hex hex then Hex (Z.of_string token)
      else fail Invalid_number span
    else if digits <> "" && is_digit digits.[0] then
      match String.split_on_char '.' digits with
      | [ whole ] when String.for_all is_digit whole -> Int (Z.of_string token)
      | [ whole; frac ] when frac <> "" && String.for_all is_digit (whole ^ frac) ->
          Float (float_of_string token)
      | _ when String.exists (fun c -> c = 'e' || c = 'E') digits -> fail Exponent span
      | _ -> fail Invalid_number span
    else if String.starts_with ~prefix:":" token then
      if token = ":" then fail Empty_keyword span
      else Keyword (String.sub token 1 (String.length token - 1))
    else
      match (token, parameter token) with
      | "true", _ -> Bool true
      | "false", _ -> Bool false
      | _, None -> Symbol token
      | _, Some n -> (
          match st.params with
          | None -> fail (Parameter_outside token) span
          | Some used ->
              if not (List.mem_assoc n used) then st.params <- Some ((n, span) :: used);
              Symbol (parameter_name n))
  in
  node form span

(* name::Type is (:: name Type): the type is the rest of the token, or the
   form right after it, as in people::[Person]. *)
and read_written st start token i =
  let at a b = { start = start + a; stop = start + b } in
  let name = node (Symbol (String.sub token 0 i)) (at 0 i) in
  let colons = node (Symbol "::") (at i (i + 2)) in
  let rest = String.sub token (i + 2) (String.length token - i - 2) in
  let ty =
    if rest <> "" then atom st (start + i + 2) rest
    else
      match peek st with
      | Some u when not (is_whitespace u || is ',' u || is ';' u || is_closing u) ->
          read_form st u
      | _ -> fail No_type colons.span
  in
  node (List [ colons; name; ty ]) (span_from st start)

let read_all source =
  let st = { source; pos = 0; params = None } in
  let rec loop acc =
    skip_blank st;
    match peek st with
    | None -> List.rev acc
    | Some u when is_closing u -> fail_here st (Unexpected_closing (Uchar.to_char u))
    | Some u -> loop (read_form st u :: acc)
  in
  try Ok (loop []) with Read_error e -> Error e

(* True when more input could complete the source (the REPL keeps reading). *)
let is_incomplete source =
  match read_all source with
  | Error { kind = Unclosed _ | Unterminated_string; _ } -> true
  | _ -> false

(* A form as source text. *)
let rec to_source (n : node) =
  let join items = String.concat " " (List.map to_source items) in
  match n.form with
  | Int i -> Z.to_string i
  | Hex i -> (if Z.sign i < 0 then "-0x" else "0x") ^ Z.format "%x" (Z.abs i)
  | Float f -> Util.float_to_string f
  | Bool b -> string_of_bool b
  | Str s -> Printf.sprintf "%S" s
  | Symbol s -> s
  | Keyword k -> ":" ^ k
  | List [ { form = Symbol "quote"; _ }; x ] -> "'" ^ to_source x
  | List [ { form = Symbol "await"; _ }; x ] -> "@" ^ to_source x
  | List [ { form = Symbol "::"; _ }; name; ty ] -> to_source name ^ "::" ^ to_source ty
  | List items -> "(" ^ join items ^ ")"
  | Vector items -> "[" ^ join items ^ "]"
  | Map entries ->
      "{"
      ^ String.concat " "
          (List.map (fun (k, v) -> to_source k ^ " " ^ to_source v) entries)
      ^ "}"
