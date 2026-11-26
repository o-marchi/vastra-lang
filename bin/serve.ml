(* vastra serve: developing a page. A folder, served to this machine only;
   every vastra.js a page asks for comes from inside this command, so it always
   matches it. Pages connect back (/.vastra/live): they hear when a file they
   loaded is saved, once it checks, and answer the REPL this terminal runs. *)

open Vastra
open Terminal
module H = Tiny_httpd

(* Every file a page loaded, by the path it asked for: the file and when it was
   last saved. Every message to the pages, in order, for all (None) or one. The
   connected pages, newest first, each with when its tab last came to the front,
   and the pages' answers to the REPL. *)
let watched : (string, string * float) Hashtbl.t = Hashtbl.create 16
let messages : (int option * string) Dynarray.t = Dynarray.create ()
let pages = ref []
let answers : (int, string) Hashtbl.t = Hashtbl.create 4
let lock = Mutex.create ()
let count = ref 0 (* numbers pages and requests *)

let fresh () =
  incr count;
  !count

(* Printed on its own line, above the REPL's input. *)
let announce = Repl.announce

(* Each HTML page served, and when it was saved as last read: a page with a
   text/vastra script that doesn't load vastra.js runs nothing, and is named
   once per save. A plain text check: <script src="vastra.js" /> passes
   it, though the browser reads the rest of that page as the script's text. *)
let read_pages : (string, float) Hashtbl.t = Hashtbl.create 8

let check_page name file saved =
  let unread =
    Mutex.protect lock (fun () ->
        let unread = Hashtbl.find_opt read_pages file <> Some saved in
        Hashtbl.replace read_pages file saved;
        unread)
  in
  if unread then
    let html = In_channel.with_open_bin file In_channel.input_all in
    (* In an attribute, so a comment that mentions vastra.js doesn't count. *)
    let loads = Util.contains html "vastra.js\"" || Util.contains html "vastra.js'" in
    if Util.contains html "text/vastra" && not loads then
      announce
        (name ^ " has a text/vastra script but no vastra.js: add "
       ^ "<script src=\"vastra.js\" defer></script>")

(* Each .vas file a page loaded, which serve checks before the page has it
  : the address it was asked for, the folder of the page that asked,
   which its modules are beside, the last version that passed in this
   run, and the files its last check read. *)
type program = {
  path : string;
  base : string;
  mutable good : string option;
  mutable reads : string list;
}

let programs : (string, program) Hashtbl.t = Hashtbl.create 8

(* The files whose last check failed, oldest first, each with its error as the
   live area shows it. One check at a time: checking sets the runtime's
   globals. *)
let broken = ref []
let checking = Mutex.create ()

let inside folder file =
  let n = String.length folder + 1 in
  if String.starts_with ~prefix:(folder ^ "/") file then
    String.sub file n (String.length file - n)
  else file

(* As `vastra build --js` checks a program: the file on its own, with the files
   it requires, and nothing typed at the prompt. *)
let check file p =
  let s = Session.create ~base_dir:p.base () in
  s.check_only <- true;
  s.run_tasks <- true;
  s.platform <- "js";
  let reads = ref [] in
  (Session.read :=
     fun path ->
       reads := path :: !reads;
       In_channel.with_open_bin path In_channel.input_all);
  (* A macro runs while checking; a Ctrl+C was for the REPL. *)
  Atomic.set Eval.stop false;
  let source =
    try In_channel.with_open_bin file In_channel.input_all with Sys_error _ -> ""
  in
  let result = Session.eval_source ~file:(inside p.base file) s source in
  p.reads <- !reads;
  (source, result)

let position source i =
  let line_start = String.rindex_from_opt source (i - 1) '\n' in
  let start = Option.fold ~none:0 ~some:succ line_start in
  let column = Diagnostic.char_count source start i + 1 in
  Printf.sprintf "%d:%d" (Diagnostic.line source i) column

(* Takes [file] as it is now if it and the files that read it check; otherwise
   it is broken. Gives the files whose version changed, or the line saying why
   it wasn't taken and its error if that is new. *)
let take file =
  Mutex.protect checking (fun () ->
      let readers =
        Hashtbl.fold
          (fun f p fs -> if f <> file && List.mem file p.reads then f :: fs else fs)
          programs []
      in
      let checked =
        List.map
          (fun f ->
            let p = Hashtbl.find programs f in
            (f, p, check f p))
          (file :: readers)
      in
      let failed = function
        | f, p, (source, Error d) -> Some (f, p, source, d)
        | _ -> None
      in
      match List.find_map failed checked with
      | None ->
          let passed (f, _) = List.mem f (file :: readers) in
          (* With a page open, its reload says so. *)
          if !pages = [] then
            List.iter
              (fun (f, _) ->
                if List.mem f (file :: readers) then
                  announce (inside (Hashtbl.find programs f).base f ^ ": taken"))
              !broken;
          broken := List.filter (fun b -> not (passed b)) !broken;
          Ok
            (List.filter_map
               (fun (_, p, (source, _)) ->
                 let changed = p.good <> Some source in
                 p.good <- Some source;
                 if changed then Some p.path else None)
               checked)
      | Some (f, p, source, d) ->
          (* Named as the page names them: from its folder. *)
          let name, source =
            match d.file with
            | Some (other, source) -> (inside p.base other, source)
            | None -> (inside p.base f, source)
          in
          let error = Diagnostic.render { d with file = Some (name, source) } "" "" in
          let fresh = List.assoc_opt file !broken <> Some error in
          broken :=
            if List.mem_assoc file !broken then
              List.map (fun (g, e) -> (g, if g = file then error else e)) !broken
            else !broken @ [ (file, error) ];
          let saved = inside (Hashtbl.find programs file).base file in
          let at () =
            let at = position source (Diagnostic.floor_boundary source d.span.start) in
            if name = saved then "at " ^ at else "in " ^ name ^ " at " ^ at
          in
          Error
            ( (if d.span.start < 0 then saved ^ ": not taken"
               else Printf.sprintf "%s: not taken, an error %s" saved (at ())),
              if fresh then Some error else None ))

(* The address pages are served at, how many saves reached them, and whether
   one has ever connected: what the status line says besides the pages. *)
let address = ref ""
let saves = ref 0
let seen = ref false

(* Each page's address as served, for the top row: counter/, about.html. *)
let names : (int, string) Hashtbl.t = Hashtbl.create 8

(* The page the REPL talks to: the one that came to the front last; of equals,
   the newest. Under [lock]. *)
let answering () =
  match !pages with
  | [] -> None
  | first :: rest ->
      let latest (p, t) (p', t') = if t' > t then (p', t') else (p, t) in
      Some (fst (List.fold_left latest first rest))

(* The top row's creature and words, from the pages and files. A
   [message] is for when there is no terminal: it prints, as it always has. *)
let tell ?pass ?message () =
  let open_, name =
    Mutex.protect lock (fun () ->
        let name = Option.bind (answering ()) (Hashtbl.find_opt names) in
        (List.length !pages, Option.value name ~default:""))
  in
  let words parts = String.concat " · " (List.filter (( <> ) "") parts) in
  let tabs = if open_ > 1 then Printf.sprintf "%d tabs" open_ else "" in
  let saved = if !saves > 0 then Printf.sprintf "↺ %d" !saves else "" in
  let pose, said =
    match !broken with
    | _ when open_ = 0 ->
        if !seen then (Creature.Asleep, words [ "every tab closed"; "open " ^ !address ])
        else (Waving, words [ "waiting for a page"; "open " ^ !address ])
    | (file, _) :: _ ->
        let file = inside (Hashtbl.find programs file).base file in
        (Drooping, words [ name; tabs; saved; "the page keeps the last good " ^ file ])
    | [] -> (Resting, words [ name; tabs; saved ])
  in
  Repl.tell_page ?pass ?message pose said

(* The live area shows the first broken file's error. *)
let show ?error () =
  Repl.show_broken ?error (match !broken with (_, error) :: _ -> Some error | [] -> None)

(* Checks the watched files a few times a second (no file-watching library). A
   saved .vas file reaches the pages only once it checks. *)
let rec watch () =
  Thread.delay 0.25;
  let saved =
    Mutex.protect lock (fun () ->
        let saved = ref [] in
        Hashtbl.filter_map_inplace
          (fun path (file, time) ->
            match (Unix.stat file).st_mtime with
            | t when t <> time ->
                saved := (path, file) :: !saved;
                Some (file, t)
            | _ -> Some (file, time)
            | exception Unix.Unix_error _ -> Some (file, time))
          watched;
        !saved)
  in
  let send kind path =
    Mutex.protect lock (fun () -> Dynarray.add_last messages (None, kind ^ "\n" ^ path))
  in
  List.iter
    (fun (path, file) ->
      if Filename.extension file <> ".vas" then send "reload" path
      else
        match take file with
        | Ok changed ->
            show ();
            List.iter (send "vas") (path :: List.filter (( <> ) path) changed);
            incr saves;
            tell ~pass:(Spinning, 1.) ()
        | Error (line, error) ->
            tell ~message:line ();
            show ?error ())
    saved;
  watch ()

(* The vastra.js this command gives pages. A page that connects with another
   (left open while serve restarted with a new build) is told to reload. *)
let build = Digest.to_hex (Digest.string Vastra_js.source)

let forget page =
  Mutex.protect lock (fun () ->
      pages := List.filter (fun (p, _) -> p <> page) !pages;
      Hashtbl.remove names page);
  tell ()

(* A page's connection: its messages since it connected, and now and then a
   ping, whose failure ends a connection the page has closed. *)
let live ~name front (module Page : H.SERVER_SENT_GENERATOR) =
  let me, start, open_ =
    Mutex.protect lock (fun () ->
        let me = fresh () in
        pages := (me, front) :: !pages;
        Hashtbl.replace names me name;
        (me, Dynarray.length messages, List.length !pages))
  in
  seen := true;
  tell ~pass:(Cheering, 1.5)
    ~message:
      (if open_ = 1 then "page connected"
       else
         Printf.sprintf
           "page connected (%d open: the REPL talks to the one you last looked at)" open_)
    ();
  let rec loop seen quiet =
    Thread.delay 0.1;
    let next =
      Mutex.protect lock (fun () ->
          List.init (Dynarray.length messages - seen) (fun i -> Dynarray.get messages (seen + i)))
    in
    List.iter
      (fun (page, data) -> if page = None || page = Some me then Page.send_event ~data ())
      next;
    if next <> [] then loop (seen + List.length next) 0
    else if quiet = 50 then (
      Page.send_event ~data:"ping" ();
      loop seen 0)
    else loop seen (quiet + 1)
  in
  (try
     Page.send_event ~data:(Printf.sprintf "page\n%d" me) ();
     loop start 0
   with _ -> ());
  forget me

(* The REPL's requests (Session.respond), answered by the page that came to the
   front last; of equals (pages never in front, say), the newest. *)
let ask url request arg =
  let send () =
    Mutex.protect lock (fun () ->
        Option.map
          (fun page ->
            let id = fresh () in
            Dynarray.add_last messages
              (Some page, Printf.sprintf "repl\n%d\n%s\n%s" id request arg);
            (id, page))
          (answering ()))
  in
  (* A page that closes before answering (its bye, or a failed ping) ends the
     wait at once. What it ran is not known, so an evaluation is run again only
     if you say so, in a tab still open. *)
  let closed () =
    let left = Mutex.protect lock (fun () -> !pages <> []) in
    if left && String.starts_with ~prefix:"eval" request then Repl.offer_again ();
    [ Session.refused
        ("the tab closed before answering, so what it ran is not known"
        ^ if left then "; another tab is open" else "") ]
  in
  let rec wait (id, page) tries =
    match
      Mutex.protect lock (fun () ->
          (Hashtbl.find_opt answers id, List.mem_assoc page !pages))
    with
    | Some answer, _ -> Session.decode answer
    | None, false -> closed ()
    | None, true when tries = 0 -> [ Session.refused "the page did not answer" ]
    | None, true ->
        Thread.delay 0.01;
        wait (id, page) (tries - 1)
  in
  let rec connected () =
    Thread.delay 0.05;
    match send () with
    | Some asked -> wait asked 1000
    | None when Atomic.get Eval.stop ->
        [ Session.refused "stopped waiting for a page: nothing ran" ]
    | None -> connected ()
  in
  (* An evaluation given before any page has connected waits for the first
    . The other requests (checks as you type, completion) don't: they
     would hold up the ones behind them. *)
  match send () with
  | Some asked -> wait asked 1000
  | None when String.starts_with ~prefix:"eval" request ->
      (* A Ctrl+C is for what was running when it came. *)
      Atomic.set Eval.stop false;
      tell ~message:("waiting for a page: open " ^ url) ();
      connected ()
  | None -> [ Session.refused ("no page is connected yet: open " ^ url) ]

(* A page's address from its connection's Referer: http://localhost:8766/counter/
   is counter/; the folder's own page is index.html. *)
let page_name req =
  match H.Request.get_header req "referer" with
  | None -> ""
  | Some url -> (
      let host = match Term.find url "://" with Some i -> i + 3 | None -> 0 in
      let path =
        match String.index_from_opt url host '/' with
        | Some i -> String.sub url i (String.length url - i)
        | None -> "/"
      in
      match List.hd (String.split_on_char '?' path) with
      | "/" -> "index.html"
      | p -> String.sub p 1 (String.length p - 1))

let run ~port folder =
  if not (Sys.file_exists folder && Sys.is_directory folder) then (
    prerr_endline ("vastra serve: there is no folder " ^ folder);
    2)
  else
    let server = H.create ~addr:"127.0.0.1" ~port () in
    H.Dir.add_dir_path ~prefix:"" ~dir:folder server
      ~config:(H.Dir.config ~dir_behavior:Index_or_lists ());
    let root = Unix.realpath folder in
    let script = Printf.sprintf "globalThis.vastraServe = %S;\n" build ^ Vastra_js.source in
    (* tiny_httpd's own check lets through a neighbour whose name starts with the
       folder's (site.txt next to site/). *)
    (* A folder's address gives its index.html in place, and is sent to the
       address ending in /, so the page's relative links resolve: what static
       hosts do. *)
    let rec file path =
      match H.Util.percent_decode path with
      | None -> `Outside
      | Some p -> (
          match Unix.realpath (Filename.concat root p) with
          | real when real <> root && not (String.starts_with ~prefix:(root ^ "/") real) ->
              `Outside
          | real when not (Sys.is_directory real) -> `File real
          | _ when String.ends_with ~suffix:"/" p -> file (path ^ "index.html")
          | _ -> `Folder
          | exception Unix.Unix_error _ -> `Missing)
    in
    (* The folder of the page asking, from its address; without one, the file's. *)
    let page_folder req real =
      let referer = H.Request.get_header req "Referer" in
      match Option.map (String.split_on_char '/') referer with
      | Some (_ :: _ :: _ :: rest) -> (
          let page = H.Util.get_non_query_path ("/" ^ String.concat "/" rest) in
          let dir =
            if String.ends_with ~suffix:"/" page then page else Filename.dirname page
          in
          let real_dir d = Unix.realpath (root ^ "/" ^ d) in
          match Option.map real_dir (H.Util.percent_decode dir) with
          | Some dir -> dir
          | None | (exception Unix.Unix_error _) -> Filename.dirname real)
      | _ -> Filename.dirname real
    in
    H.add_middleware server ~stage:(`Stage 1) (fun handler req ~resp ->
        let path = H.Util.get_non_query_path req.H.Request.path in
        (* While developing, the browser asks again every time. *)
        let resp r = resp (H.Response.set_header "Cache-Control" "no-store" r) in
        if Filename.basename path = "vastra.js" then
          resp
            (H.Response.make_string ~headers:[ ("Content-Type", "text/javascript") ] (Ok script))
        else
          match file path with
          | `Outside -> resp (H.Response.make_raw ~code:403 "outside the served folder")
          | `Folder ->
              resp (H.Response.make_void ~code:301 ~headers:[ ("Location", path ^ "/") ] ())
          | `File real ->
              if Filename.extension real = ".vas" then
                Mutex.protect checking (fun () ->
                    if not (Hashtbl.mem programs real) then
                      Hashtbl.replace programs real
                        { path; base = page_folder req real; good = None; reads = [] });
              let saved = (Unix.stat real).st_mtime in
              Mutex.protect lock (fun () ->
                  if not (Hashtbl.mem watched path) then
                    Hashtbl.replace watched path (real, saved));
              if List.mem (Filename.extension real) [ ".html"; ".htm" ] then
                check_page (inside root real) real saved;
              (* Types tiny_httpd does not know: an .svg image is drawn, and an
                 npm package's .mjs module runs, which a browser refuses without
                 its type. *)
              let typed t = handler req ~resp:(fun r -> resp (H.Response.set_header "Content-Type" t r)) in
              (match Filename.extension real with
              (* tiny_httpd would send a folder's address to its index.html. *)
              | _ when String.ends_with ~suffix:"/" path ->
                  let html = In_channel.with_open_bin real In_channel.input_all in
                  resp
                    (H.Response.make_string ~headers:[ ("Content-Type", "text/html") ] (Ok html))
              (* The version that passed last, or an empty program;
                 shown as text, not downloaded. *)
              | ".vas" ->
                  (match take real with
                  | Ok _ -> show ()
                  | Error (_, error) -> show ?error ());
                  let good = (Hashtbl.find programs real).good in
                  resp
                    (H.Response.make_string
                       ~headers:[ ("Content-Type", "text/plain; charset=utf-8") ]
                       (Ok (Option.value good ~default:"")))
              | ".svg" -> typed "image/svg+xml"
              | ".mjs" -> typed "text/javascript"
              | ".png" -> typed "image/png"
              | _ -> handler req ~resp)
          | `Missing -> handler req ~resp);
    H.add_route_server_sent_handler server
      H.Route.(exact ".vastra" @/ exact "live" @/ return)
      (fun req (module Page : H.SERVER_SENT_GENERATOR) ->
        let query = H.Request.query req in
        if List.assoc_opt "build" query = Some build then
          live ~name:(page_name req)
            (Option.value ~default:0 (Option.bind (List.assoc_opt "front" query) int_of_string_opt))
            (module Page)
        else (
          tell ~message:"a page running an older vastra.js connected: reloading it" ();
          Page.send_event ~data:"reload\n" ()));
    H.add_route_handler ~meth:`POST server
      H.Route.(exact ".vastra" @/ exact "say" @/ return)
      (fun req ->
        announce req.H.Request.body;
        H.Response.make_string (Ok ""));
    (* A page's tab came to the front, or the page went away. *)
    H.add_route_handler ~meth:`POST server
      H.Route.(exact ".vastra" @/ exact "front" @/ return)
      (fun req ->
        (match List.map int_of_string_opt (String.split_on_char '\n' req.H.Request.body) with
        | [ Some page; Some time ] ->
            let open_ =
              Mutex.protect lock (fun () ->
                  let came (p, t) = if p = page then (p, time) else (p, t) in
                  pages := List.map came !pages;
                  List.length !pages)
            in
            (* The creature glances at the tab that answers now. *)
            if open_ > 1 then tell ~pass:(Looking, 1.) ()
        | _ -> ());
        H.Response.make_string (Ok ""));
    H.add_route_handler ~meth:`POST server
      H.Route.(exact ".vastra" @/ exact "bye" @/ return)
      (fun req ->
        Option.iter forget (int_of_string_opt req.H.Request.body);
        H.Response.make_string (Ok ""));
    H.add_route_handler ~meth:`POST server
      H.Route.(exact ".vastra" @/ exact "answer" @/ return)
      (fun req ->
        let body = req.H.Request.body in
        (match String.index_opt body '\n' with
        | Some i ->
            Mutex.protect lock (fun () ->
                Hashtbl.replace answers
                  (int_of_string (String.sub body 0 i))
                  (String.sub body (i + 1) (String.length body - i - 1)))
        | None -> ());
        H.Response.make_string (Ok ""));
    let status = Atomic.make `Starting in
    let thread =
      Thread.create
        (fun () ->
          match H.run ~after_init:(fun () -> Atomic.set status `Ready) server with
          | Ok () -> ()
          | Error e -> Atomic.set status (`Failed e))
        ()
    in
    let rec started () =
      match Atomic.get status with
      | `Starting ->
          Thread.delay 0.01;
          started ()
      | s -> s
    in
    match started () with
    | `Failed (Unix.Unix_error (Unix.EADDRINUSE, _, _)) ->
        prerr_endline
          (Printf.sprintf "vastra serve: port %d is in use; choose another with --port N"
             port);
        1
    | `Failed (Unix.Unix_error (e, _, _)) ->
        prerr_endline
          (Printf.sprintf "vastra serve: port %d can't be served: %s" port
             (Unix.error_message e));
        1
    | `Failed e ->
        prerr_endline
          (Diagnostic.render (Diagnostic.bug Diagnostic.nowhere (Printexc.to_string e)) "" "");
        1
    | _ ->
        ignore (Thread.create watch ());
        let url = Printf.sprintf "http://localhost:%d" port in
        address := url;
        tell ();
        let banner =
          Printf.sprintf
            "Serving %s at %s\n\
             This terminal is a REPL into the page you last looked at. Ctrl+D stops."
            folder url
        in
        let code = Repl.run ~about:banner (ask url) in
        (* Without a terminal (in the background, say), serve on after the input ends. *)
        if not (Unix.isatty Unix.stdin) then Thread.join thread;
        code
