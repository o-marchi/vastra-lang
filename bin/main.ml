open Vastra

let max_depth = 100_000

let usage =
  "usage: vastra [FILE]                  run FILE, printing each result (no FILE: the REPL)\n\
  \       vastra run FILE ARGS          run FILE as a program: its tasks run, with ARGS\n\
  \       vastra build [--show] [--js] FILE [-o OUT]\n\
  \                                    compile FILE to a native program (like `run`;\n\
  \                                    with --show, like printing each result;\n\
  \                                    with --js, to JavaScript for a page or Node)\n\
  \       vastra serve [--port N] [FOLDER]\n\
  \                                    develop a web page: serve FOLDER (default: this\n\
  \                                    folder) at http://localhost:8000 (or port N);\n\
  \                                    saved files reload in the page, and this\n\
  \                                    terminal is a REPL into it"

(* A command line that doesn't fit: what is wrong, and where the usage is. *)
let wrong what =
  prerr_endline (what ^ "\nvastra --help shows how vastra is used");
  2

let read_file path =
  match In_channel.with_open_bin path In_channel.input_all with
  | s when String.is_valid_utf_8 s -> Ok s
  | _ -> Error "stream did not contain valid UTF-8"
  | exception Sys_error m ->
      let prefix = path ^ ": " in
      Error
        (if String.starts_with ~prefix m then
           String.sub m (String.length prefix) (String.length m - String.length prefix)
         else m)

(* Loads [path]; [report] shows the outcomes; gives the exit status. *)
(* The terminal's width, when results go to one. *)
let width =
  lazy
    (if not (Unix.isatty Unix.stdout) then None
     else
       let size = Unix.open_process_in "stty size < /dev/tty 2>/dev/null" in
       let cols =
         try Scanf.sscanf (input_line size) "%d %d" (fun _ c -> Some c) with _ -> None
       in
       ignore (Unix.close_process_in size);
       cols)

let run path ~program (report : string -> Session.outcome list -> int) =
  match read_file path with
  | Error m ->
      prerr_endline (Printf.sprintf "cannot read %s: %s" path m);
      1
  | Ok source -> (
      let session = Session.create ~max_depth ~base_dir:(Filename.dirname path) () in
      session.run_tasks <- program;
      if not program then session.width <- Lazy.force width;
      match Session.eval_source ~file:path session source with
      | Ok outcomes -> report source outcomes
      | Error d ->
          prerr_endline (Diagnostic.render d source path);
          1)

let show _ outcomes =
  let width = Lazy.force width in
  List.iter (fun o -> print_endline (Session.outcome_to_string ?width o)) outcomes;
  0

(* A program prints only through its tasks; an unhandled task error ends it. *)
let program path source outcomes =
  match List.find_map (function Session.Failed (e, s) -> Some (e, s) | _ -> None) outcomes with
  | Some (error, span) ->
      prerr_endline (Diagnostic.render (Diagnostic.untaken span error) source path);
      1
  | None -> !Builtins.exit_code

(* Generates OCaml and compiles it with ocamlfind against the installed vastra library. *)
let build ~show ~js path out =
  match read_file path with
  | Error m ->
      prerr_endline (Printf.sprintf "cannot read %s: %s" path m);
      1
  | Ok source -> (
      match Compile.program ~show ~js path source with
      | Error d ->
          prerr_endline (Diagnostic.render d source path);
          1
      | Ok (code, library) ->
          let dir = Filename.temp_dir "vastra-build" "" in
          let main = Filename.concat dir "main.ml" in
          Out_channel.with_open_text main (fun oc -> output_string oc code);
          let q = Filename.quote in
          let command =
            if js then
              let byte = Filename.concat dir "main.byte" in
              Printf.sprintf
                "ocamlfind ocamlc -package %s -linkpkg %s -o %s 2> %s/errors && \
                 js_of_ocaml \"$(ocamlfind query zarith_stubs_js)/runtime.js\" \
                 \"$(ocamlfind query mtime.clock)/runtime.js\" %s -o %s 2>> %s/errors"
                library (q main) (q byte) (q dir) (q byte) (q out) (q dir)
            else
              Printf.sprintf
                "ocamlfind ocamlopt -package %s -linkpkg %s -o %s 2> %s/errors" library
                (q main) (q out) (q dir)
          in
          if Sys.command command = 0 then 0
          else (
            prerr_endline ("vastra build: the OCaml compiler failed; see " ^ dir);
            1))

let () =
  Vastra_window.install ();
  exit
    (match List.tl (Array.to_list Sys.argv) with
    | [] ->
        let session = Session.create ~max_depth () in
        session.run_tasks <- true;
        Repl.run (Session.respond session)
    | [ ("--help" | "-h") ] ->
        print_endline usage;
        0
    | "run" :: path :: args ->
        Builtins.program_args := args;
        (Builtins.ending := fun () -> exit !Builtins.exit_code);
        run path ~program:true (program path)
    | "build" :: rest -> (
        let show = List.mem "--show" rest and js = List.mem "--js" rest in
        let rest = List.filter (fun a -> a <> "--show" && a <> "--js") rest in
        match rest with
        | [ path ] ->
            build ~show ~js path
              (Filename.remove_extension path ^ if js then ".js" else "")
        | [ path; "-o"; out ] -> build ~show ~js path out
        | [] -> wrong "vastra build: which file? as in vastra build game.vas"
        | _ -> wrong ("vastra build: unknown arguments: " ^ String.concat " " rest))
    | "serve" :: rest -> (
        let port, rest =
          match rest with
          | "--port" :: n :: rest -> (int_of_string_opt n, rest)
          | rest -> (Some 8000, rest)
        in
        match (port, rest) with
        | Some port, [] -> Serve.run ~port "."
        | Some port, [ folder ] -> Serve.run ~port folder
        | None, _ -> wrong "vastra serve: --port takes a number, as in --port 8080"
        | Some _, _ -> wrong "vastra serve: one folder at most")
    | [ "run" ] -> wrong "vastra run: which file? as in vastra run game.vas"
    | [ path ] -> run path ~program:false show
    | first :: _ ->
        wrong
          (Printf.sprintf
             "vastra: `%s` is not a command: they are run, build and serve"
             first))
