(* JSON text → the Json type of the module vastra.json, as an Vastra Result. *)

open Value

exception Bad of string

let ctor name args = Ctor ("vastra.json/" ^ name, args)

(* A native told a written type is given its description first. *)
type Value.opaque += Shape of Shape.t

(* A platform's value as Json, set by a runtime that has some: JavaScript's.
   Given the shape decoded to, so that it reads only what the shape names. *)
let of_opaque : (Shape.t -> Value.opaque -> t) ref =
  ref (fun _ _ -> raise (Internal "not data"))

let told shape = function
  | Builtin b ->
      Builtin { b with run = (fun args -> b.run (Opaque (Shape shape) :: args)) }
  | _ -> raise (Internal "a type told to what is not a native")

let parse text =
  let pos = ref 0 in
  let peek () = if !pos < String.length text then Some text.[!pos] else None in
  let fail what = raise (Bad (Printf.sprintf "%s at character %d" what (!pos + 1))) in
  let rec blank () =
    match peek () with
    | Some (' ' | '\n' | '\r' | '\t') ->
        incr pos;
        blank ()
    | _ -> ()
  in
  let starts s =
    !pos + String.length s <= String.length text
    && String.sub text !pos (String.length s) = s
  in
  let expect s =
    if
      !pos + String.length s <= String.length text
      && String.sub text !pos (String.length s) = s
    then pos := !pos + String.length s
    else fail ("expected " ^ s)
  in
  (* The four hex digits of a \u escape, as a UTF-16 code unit. *)
  let hex4 () =
    let digits = if !pos + 4 <= String.length text then String.sub text !pos 4 else "" in
    let hex = function '0' .. '9' | 'a' .. 'f' | 'A' .. 'F' -> true | _ -> false in
    if digits = "" || not (String.for_all hex digits) then fail "invalid \\u escape";
    pos := !pos + 4;
    int_of_string ("0x" ^ digits)
  in
  let string () =
    expect "\"";
    let b = Buffer.create 16 in
    let rec go () =
      match peek () with
      | None -> fail "unterminated string"
      | Some '"' -> incr pos
      | Some '\\' -> (
          incr pos;
          let c = peek () in
          incr pos;
          match c with
          | Some ('"' | '\\' | '/') ->
              Buffer.add_char b (Option.get c);
              go ()
          | Some 'n' ->
              Buffer.add_char b '\n';
              go ()
          | Some 't' ->
              Buffer.add_char b '\t';
              go ()
          | Some 'r' ->
              Buffer.add_char b '\r';
              go ()
          | Some 'b' ->
              Buffer.add_char b '\b';
              go ()
          | Some 'f' ->
              Buffer.add_char b '\012';
              go ()
          | Some 'u' ->
              (* Beyond U+FFFF, a character is two escapes: a UTF-16 surrogate pair. *)
              let start = !pos in
              let code =
                match hex4 () with
                | high when high >= 0xD800 && high < 0xDC00 && starts "\\u" -> (
                    pos := !pos + 2;
                    match hex4 () with
                    | low when low >= 0xDC00 && low < 0xE000 ->
                        0x10000 + ((high - 0xD800) lsl 10) + (low - 0xDC00)
                    | _ -> high (* still half a pair: rejected below *))
                | code -> code
              in
              if not (Uchar.is_valid code) then (
                pos := start;
                fail "invalid \\u escape");
              Buffer.add_utf_8_uchar b (Uchar.of_int code);
              go ()
          | _ -> fail "invalid escape")
      | Some c ->
          Buffer.add_char b c;
          incr pos;
          go ()
    in
    go ();
    Buffer.contents b
  in
  let rec value () =
    blank ();
    match peek () with
    | Some '{' ->
        incr pos;
        blank ();
        let rec fields acc =
          blank ();
          let k = string () in
          blank ();
          expect ":";
          let v = value () in
          blank ();
          let acc = dict_insert (Str k) v acc in
          match peek () with
          | Some ',' ->
              incr pos;
              fields acc
          | _ ->
              expect "}";
              acc
        in
        if peek () = Some '}' then (
          incr pos;
          ctor "JObject" [ Dict [] ])
        else ctor "JObject" [ Dict (fields []) ]
    | Some '[' ->
        incr pos;
        blank ();
        let rec items acc =
          let v = value () in
          blank ();
          match peek () with
          | Some ',' ->
              incr pos;
              items (v :: acc)
          | _ ->
              expect "]";
              List.rev (v :: acc)
        in
        if peek () = Some ']' then (
          incr pos;
          ctor "JArray" [ Vector [||] ])
        else ctor "JArray" [ Vector (Array.of_list (items [])) ]
    | Some '"' -> ctor "JString" [ Str (string ()) ]
    | Some ('t' | 'f' | 'n') -> (
        match
          List.find_opt
            (fun (word, _) -> starts word)
            [
              ("true", ctor "JBool" [ Bool true ]);
              ("false", ctor "JBool" [ Bool false ]);
              ("null", ctor "JNull" []);
            ]
        with
        | Some (word, v) ->
            pos := !pos + String.length word;
            v
        | None -> fail "expected a JSON value")
    | Some ('-' | '0' .. '9') -> (
        let start = !pos in
        while
          match peek () with
          | Some ('-' | '+' | '.' | 'e' | 'E' | '0' .. '9') -> true
          | _ -> false
        do
          incr pos
        done;
        match float_of_string_opt (String.sub text start (!pos - start)) with
        | Some f -> ctor "JNumber" [ Float f ]
        | None -> fail "invalid number")
    | _ -> fail "expected a JSON value"
  in
  match
    let v = value () in
    blank ();
    if !pos <> String.length text then fail "unexpected text after the JSON value";
    v
  with
  | v -> Ctor ("Ok", [ v ])
  | exception Bad message -> Ctor ("Err", [ Str message ])

(* [j], a Json value, as a value of the written type [shape], or why it
   isn't one, saying where: in [1].gender: expected a string, found a number. *)
let decode (shape : Shape.t) j =
  let quoted s = "\"" ^ escape s ^ "\"" in
  let rec alternatives = function
    | [ a; b ] -> a ^ " or " ^ b
    | a :: (_ :: _ as rest) -> a ^ ", " ^ alternatives rest
    | words -> String.concat "" words
  in
  let found = function
    | Ctor ("vastra.json/JString", [ Str s ]) -> quoted s
    | Ctor ("vastra.json/JNull", []) -> "null"
    | Ctor ("vastra.json/JBool", _) -> "a boolean"
    | Ctor ("vastra.json/JNumber", _) -> "a number"
    | Ctor ("vastra.json/JArray", _) -> "an array"
    | _ -> "an object"
  in
  (* [path]: where [j] is, innermost first, as [1] and .gender. *)
  let rec go path (shape : Shape.t) j =
    let fail what =
      let where = String.concat "" (List.rev path) in
      let where =
        if String.starts_with ~prefix:"." where then
          String.sub where 1 (String.length where - 1)
        else where
      in
      raise (Bad (if where = "" then what else Printf.sprintf "in %s: %s" where what))
    in
    let expected what = fail (Printf.sprintf "expected %s, found %s" what (found j)) in
    match (shape, j) with
    | Json, _ -> j
    | String, Ctor ("vastra.json/JString", [ s ]) -> s
    | Bool, Ctor ("vastra.json/JBool", [ b ]) -> b
    | Float, Ctor ("vastra.json/JNumber", [ f ]) -> f
    | Int, Ctor ("vastra.json/JNumber", [ Float f ]) when Float.is_integer f ->
        Int (Z.of_float f)
    | Option _, Ctor ("vastra.json/JNull", []) -> Ctor ("None", [])
    | Option s, _ -> Ctor ("Some", [ go path s j ])
    | Vector s, Ctor ("vastra.json/JArray", [ Vector items ]) ->
        Vector (Array.mapi (fun i x -> go (Printf.sprintf "[%d]" i :: path) s x) items)
    | Record keys, Ctor ("vastra.json/JObject", [ Dict entries ]) ->
        (* Outside, a key that may be missing is named without its ?. *)
        let field (k, s) =
          let name = if Util.may_miss k then String.sub k 0 (String.length k - 1) else k in
          match List.assoc_opt (Str name) entries with
          | Some x -> Some (k, go (("." ^ name) :: path) s x)
          | None when Util.may_miss k -> None
          | None -> fail (Printf.sprintf "missing field \"%s\"" name)
        in
        Record (List.filter_map field keys)
    | Words words, _ -> (
        let given =
          match j with Ctor ("vastra.json/JString", [ Str w ]) -> Some w | _ -> None
        in
        match List.find_opt (fun (_, w) -> Some w = given) words with
        | Some (ctor, _) -> Ctor (ctor, [])
        | None -> expected (alternatives (List.map (fun (_, w) -> quoted w) words)))
    | String, _ -> expected "a string"
    | Bool, _ -> expected "a boolean"
    | Float, _ -> expected "a number"
    | Int, _ -> expected "a whole number"
    | Vector _, _ -> expected "an array"
    | Record _, _ -> expected "an object"
  in
  let j = match j with Opaque o -> !of_opaque shape o | j -> j in
  match go [] shape j with
  | v -> Ctor ("Ok", [ v ])
  | exception Bad why -> Ctor ("Err", [ Str why ])
