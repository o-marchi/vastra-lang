(* The page's side of vastra serve: reloads the scripts serve says were
   saved, and answers the REPL in serve's terminal. Only vastra.js links this,
   and it connects only when vastra serve gave the page its vastra.js (which
   then sets vastraServe to its build, which the page sends back). *)

open Js_of_ocaml
open Vastra

let post path text =
  let xhr = XmlHttpRequest.create () in
  xhr##_open (Js.string "POST") (Js.string path) Js._true;
  xhr##send (Js.some (Js.string text))

(* Printed in vastra serve's terminal. *)
let say text = post "/.vastra/say" text

let pathname url =
  let url =
    Js.Unsafe.new_obj Js.Unsafe.global##._URL
      [|
        Js.Unsafe.inject (Js.string url);
        Js.Unsafe.inject Dom_html.window##.location##.href;
      |]
  in
  Js.to_string url##.pathname

(* When the top-level expressions are the same, the lines that changed start
   again, with the values computed from them, and the others keep their values.
   Otherwise the script starts again from a fresh session. Serve sends
   only saves that check, with the files that require them. After a saved
   module, the script's file is taken again, since it uses the module. *)
let reload (script : Vastra_web.script) saved =
  let source = Vastra_web.read script.url in
  let s = script.session in
  let changed = ref [] and notes = ref [] and restarted = ref [] and fresh = ref [] in
  let take why file =
    if why <> None then why
    else
      let text = if file = script.url then source else Vastra_web.read file in
      s.definitions_only <- true;
      let result = Session.eval_source ~fresh:!fresh ~file s text in
      s.definitions_only <- false;
      changed := !changed @ s.changed;
      notes := !notes @ s.notes;
      restarted := !restarted @ s.restarted;
      fresh := s.fresh;
      let mine = List.filter (fun (f, _) -> f = Some file) in
      match result with
      | Ok _ when mine s.expressions <> mine script.expressions ->
          Some "a top-level expression changed"
      | Ok _ ->
          let others = List.filter (fun (f, _) -> f <> Some file) script.expressions in
          script.expressions <- others @ s.expressions;
          None
      | Error d -> Some ("the running page cannot take it:\n" ^ Diagnostic.render d text file)
  in
  let files = (if saved = script.url then [] else [ saved ]) @ [ script.url ] in
  (* A file whose ns changed moves every name, so the page starts again. *)
  let module_of text =
    Result.fold ~ok:Session.module_of ~error:(fun _ -> None) (Reader.read_all text)
  in
  let moved = module_of script.source <> module_of source in
  let why = List.fold_left take (if moved then Some "its ns changed" else None) files in
  script.source <- source;
  Vastra_web.clear_errors ();
  (* A replay or a loop that is playing stops at a change of type. *)
  let stopped =
    match (why, !Vastra_web.activity) with
    | None, Some a when !changed <> [] && a.playing ->
        Vastra_web.finish a;
        [ "note: the replay stopped: the type of its names or messages changed" ]
    | _ -> []
  in
  match why with
  | None when !changed <> [] ->
      say
        (String.concat "\n"
           (Printf.sprintf "%s: reloaded; %s changed type" saved
              (String.concat ", " (List.map (Printf.sprintf "`%s`") !changed))
           :: (!notes @ stopped)))
  | None ->
      Vastra_web.render_all ();
      (* What started again; the others keep their values. *)
      let names = List.map (Printf.sprintf "`%s`") !restarted in
      say
        (String.concat "\n"
           ((if names = [] then saved ^ ": reloaded, state kept"
             else
               Printf.sprintf "%s: reloaded; %s started again" saved
                 (String.concat ", " names))
           :: !notes))
  | Some why ->
      let fresh = Vastra_web.session () in
      script.session <- fresh;
      Vastra_web.run_script fresh ~origin:script.url source;
      script.expressions <- fresh.expressions;
      say (Printf.sprintf "%s: started again, because %s" saved why)

(* While a REPL request runs, what the page prints goes into its answer;
   otherwise to serve's terminal. Either way, also to the browser's console. *)
let captured = ref None

let printed text =
  Console.console##log (Js.string text);
  match !captured with Some b -> Buffer.add_string b text | None -> say text

let first_line text =
  match String.index_opt text '\n' with
  | Some i -> (String.sub text 0 i, String.sub text (i + 1) (String.length text - i - 1))
  | None -> (text, "")

(* The REPL's session: that of the page's last script, or one of its own. *)
let session () =
  match List.rev !Vastra_web.scripts with
  | script :: _ -> script.session
  | [] -> Lazy.force Vastra_web.repl

let answer message =
  let id, rest = first_line message in
  let request, arg = first_line rest in
  let s = session () in
  let buffer = Buffer.create 64 in
  captured := Some buffer;
  let parts = Session.respond s request arg in
  captured := None;
  let ok = String.starts_with ~prefix:"eval" request && not (List.exists (function Session.Problem _ -> true | _ -> false) parts) in
  let note =
    if ok && s.changed <> [] && (!Value.views <> [] || !Value.handlers <> []) then
      [
        Session.Note
          (Printf.sprintf
             "note: %s changed type; the running program keeps the version it started with \
              (save the file to start it again)"
             (String.concat ", " (List.map (Printf.sprintf "`%s`") s.changed)));
      ]
    else []
  in
  if ok then Vastra_web.render_all ();
  let output = Buffer.contents buffer in
  let output =
    if String.ends_with ~suffix:"\n" output then String.sub output 0 (String.length output - 1)
    else output
  in
  let printed = if output = "" then [] else [ Session.Output output ] in
  post "/.vastra/answer" (id ^ "\n" ^ Session.encode (printed @ parts @ note))

(* This page's number at serve, and when this tab last came to the front, kept
   across reloads: serve's REPL talks to the page that came to the front last. *)
let me = ref ""

let storage () = try Js.Optdef.to_option Dom_html.window##.sessionStorage with _ -> None

let front =
  ref
    (match storage () with
    | Some s -> Js.Opt.case (s##getItem (Js.string "vastra-front")) (fun () -> "0") Js.to_string
    | None -> "0")

let came_to_front () =
  front := Printf.sprintf "%.0f" (Js.to_float (new%js Js.date_now)##getTime);
  Option.iter (fun s -> s##setItem (Js.string "vastra-front") (Js.string !front)) (storage ());
  if !me <> "" then post "/.vastra/front" (!me ^ "\n" ^ !front)

(* Messages from serve: a first line saying what, then what it is about. *)
let receive message =
  let kind, rest = first_line message in
  match kind with
  | "page" -> me := rest
  | "vas" ->
      List.iter
        (fun (script : Vastra_web.script) ->
          let files = script.url :: Session.files script.session in
          List.iter (fun file -> if pathname file = rest then reload script file) files)
        !Vastra_web.scripts
  | "reload" -> Dom_html.window##.location##reload
  | "repl" -> answer rest
  | _ -> ()

let connect () =
  let build : Js.js_string Js.t Js.Optdef.t = Js.Unsafe.global##.vastraServe in
  Js.Optdef.iter build (fun build ->
    Sys_js.set_channel_flusher stdout printed;
    Sys_js.set_channel_flusher stderr printed;
    let document = Js.Unsafe.inject Dom_html.document in
    if Js.to_bool (Js.Unsafe.meth_call document "hasFocus" [||]) then came_to_front ();
    let on target event f =
      ignore
        (Dom_html.addEventListener target (Dom_html.Event.make event)
           (Dom_html.handler (fun _ -> f (); Js._true))
           Js._false)
    in
    on Dom_html.window "focus" came_to_front;
    on Dom_html.document "visibilitychange" (fun () ->
        if Js.to_string (Js.Unsafe.get document "visibilityState") = "visible" then
          came_to_front ());
    (* Gone at once, rather than when serve's next ping fails. *)
    on Dom_html.window "pagehide" (fun () ->
        ignore
          (Js.Unsafe.meth_call Dom_html.window##.navigator "sendBeacon"
             [| Js.Unsafe.inject (Js.string "/.vastra/bye"); Js.Unsafe.inject (Js.string !me) |]));
    let events =
      new%js EventSource.eventSource
        (Js.string
           (Printf.sprintf "/.vastra/live?build=%s&front=%s" (Js.to_string build) !front))
    in
    events##.onmessage :=
      Dom.handler (fun event ->
          receive (Js.to_string event##.data);
          Js._true))
