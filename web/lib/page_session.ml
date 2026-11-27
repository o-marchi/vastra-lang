(* Vastra's checker and interpreter in a page: vastra.js runs the page's
   <script type="text/vastra"> programs with them, and browser/submit is a
   page's REPL into itself. A build links this only if its program submits. *)

open Js_of_ocaml
open Vastra
open Value
open Vastra_web

let session () =
  let s = Session.create () in
  s.platform <- "js";
  s.run_tasks <- true;
  s

(* The ES modules a page's program imports, its Vastra modules' too. *)
let rec imports ?(seen = ref []) source =
  match Reader.read_all source with
  | Ok (first :: _) -> (
      match Analyze.analyze_top ~trusted:false first with
      | Ns { imports = own; requires; _ } ->
          let theirs (r : Ast.require) =
            if List.mem r.module_ !seen || Stdlib_sources.find r.module_ <> None then []
            else (
              seen := r.module_ :: !seen;
              let slash c = if c = '.' then '/' else c in
              imports ~seen (read (String.map slash r.module_ ^ ".vas")))
          in
          List.map (fun (i : Ast.import) -> i.spec) own @ List.concat_map theirs requires
      | _ -> []
      | exception Diagnostic.Error _ -> [])
  | _ -> []

let run_script s ~origin source =
  guard ~source ~origin (fun () ->
      match Session.eval_source ~file:origin s source with
      | Ok _ -> ()
      | Error d -> show_error (Diagnostic.render d source origin))

(* The page's scripts that come from a file, for vastra serve to reload,
   with the text of the top-level expressions of its files, its modules' too,
   when they last ran (the session's own record follows the REPL's submissions
   too), and the file's text then. *)
type script = {
  url : string;
  mutable session : Session.t;
  mutable expressions : (string option * string) list;
  mutable source : string;
}

let scripts : script list ref = ref []

(* What a recording starts from: the names the page's file changes. *)
let () =
  cells :=
    fun () ->
      match List.rev !scripts with script :: _ -> Session.cells script.session | [] -> []

(* The page's programs run once the ES modules they import are loaded. *)
let run_scripts () =
  let found = document##querySelectorAll (Js.string "script[type=\"text/vastra\"]") in
  let program i =
    let script = Js.Opt.get (found##item i) (fun () -> raise Not_found) in
    match Js.Opt.to_option (script##getAttribute (Js.string "src")) with
    | Some url -> (Some (Js.to_string url), read (Js.to_string url))
    | None ->
        (None, Js.to_string (Js.Opt.get script##.textContent (fun () -> Js.string "")))
  in
  let programs = List.init found##.length program in
  preload
    (List.concat_map (fun (_, source) -> imports source) programs)
    (fun () ->
      List.iter
        (fun (url, source) ->
          let s = session () in
          match url with
          | Some url ->
              run_script s ~origin:url source;
              let script = { url; session = s; expressions = s.expressions; source } in
              scripts := !scripts @ [ script ]
          | None -> run_script s ~origin:"page" source)
        programs)

(* The REPL hook: vastra.eval(source) gives what the REPL would print. *)
let repl = lazy (session ())

let eval source =
  let s = Lazy.force repl in
  match Session.eval_source s source with
  | Ok outcomes -> String.concat "\n" (List.map Session.outcome_to_string outcomes)
  | Error d -> Diagnostic.render d source "repl"
  | exception e -> "internal error: " ^ Printexc.to_string e

(* browser/submit: a page's REPL into itself. The source goes to the
   page's session as from vastra serve's terminal, on a later turn, so
   the program asking has finished its own turn first. *)
let submit = function
  | [ Str source ] ->
      Task
        (fun k ->
          let later () =
            let s =
              match List.rev !scripts with
              | script :: _ -> script.session
              | [] -> Lazy.force repl
            in
            let reply c args = ctor ("vastra.browser/" ^ c) (List.map (fun t -> Str t) args) in
            let shown = function
              | Session.Outcome (Defined { name; ty }) -> reply "Value" [ name; ty ]
              | Outcome (Evaluated { value; ty }) -> reply "Value" [ value; ty ]
              | Outcome (Failed (e, _)) -> reply "Problem" [ "task failed: " ^ e ]
              | Problem p -> reply "Problem" [ p.text ]
              | Outcome (Declared t) | Note t | Output t -> reply "Note" [ t ]
            in
            let parts = Session.respond s "eval 60" source in
            render_all ();
            k (Ok (Vector (Array.of_list (List.map shown parts))))
          in
          ignore (Dom_html.setTimeout later 0.))
  | _ -> raise (Internal "browser/submit")

(* The interpreter reaches the page's ES modules, and browser/submit is provided. *)
let install () =
  (Session.imported :=
     fun spec -> Option.map (fun v -> Opaque (Js v)) (Hashtbl.find_opt modules spec));
  Builtins.extra :=
    ("vastra.browser/submit", Builtin { builtin_name = "submit"; run = submit })
    :: !Builtins.extra

(* The page runtime: runs the page's scripts, and offers vastra.eval for a REPL. *)
let run_page () =
  (Session.read :=
     fun path ->
       match load path with
       | status, text when status / 100 = 2 -> text
       | _ -> raise (Sys_error path));
  set global "vastra"
    (Js.Unsafe.obj
       [|
         ( "eval",
           Js.Unsafe.inject
             (Js.wrap_callback (fun s -> Js.string (eval (Js.to_string s)))) );
         ("send", Js.Unsafe.inject (Js.Unsafe.callback_with_arguments send));
       |]);
  if Js.to_string document##.readyState = "loading" then
    ignore
      (Dom_html.addEventListener document
         (Dom_html.Event.make "DOMContentLoaded")
         (Dom_html.handler (fun _ ->
              run_scripts ();
              Js._true))
         Js._false)
  else run_scripts ()
