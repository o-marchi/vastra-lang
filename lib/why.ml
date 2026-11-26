(* The long form of a rule an error states, by the key the error names:
   a section of why.txt. *)

let sections =
  lazy
    (let sections = ref [] and key = ref None and lines = ref [] in
     let close () =
       Option.iter
         (fun k ->
           let text = String.trim (String.concat "\n" (List.rev !lines)) in
           sections := (k, text) :: !sections)
         !key
     in
     List.iter
       (fun line ->
         if String.starts_with ~prefix:"## " line then (
           close ();
           key := Some (String.sub line 3 (String.length line - 3));
           lines := [])
         else lines := line :: !lines)
       (String.split_on_char '\n' Why_source.source);
     close ();
     !sections)

let explain key = List.assoc_opt key (Lazy.force sections)
