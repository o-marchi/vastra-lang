(* A printed program takes the runtime.js paragraphs it uses, and those they
   name, by name. So every paragraph has a name the printer reads, and every
   name it uses is another paragraph's, the platform's or a constructor's:
   anything else would be missing from a program when it ran. *)

let platform =
  [ "Array"; "ArrayBuffer"; "BigInt"; "Date"; "Error"; "Math"; "Number"; "Object"; "Set"; "String";
    "TextDecoder"; "TextEncoder"; "URL"; "Uint32Array"; "clearTimeout"; "console"; "crypto";
    "document"; "fetch"; "globalThis"; "parseInt"; "performance"; "process"; "setTimeout";
    "undefined" ]

(* Vastra's, which a program defines when the runtime it takes names them. *)
let constructors = [ "None"; "Some"; "Ok"; "Err"; "Text" ]

let () =
  let paragraphs = Vastra_javascript.paragraphs () in
  let named = List.filter (( <> ) "") (List.map fst paragraphs) in
  let known u = List.mem u named || List.mem u platform || List.mem u constructors in
  let problems (name, code) =
    if name = "" then [ "a paragraph with no name the printer reads:\n" ^ code ]
    else
      List.filter_map
        (fun u -> if known u then None else Some (name ^ " uses " ^ u ^ ", which no paragraph defines"))
        (Vastra_javascript.undeclared code)
  in
  match List.concat_map problems paragraphs with
  | [] -> ()
  | found ->
      List.iter (fun p -> prerr_endline ("FAILED: " ^ p)) found;
      exit 1
