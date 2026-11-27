(* Vastra in the browser: what the browser modules declare (JavaScript calls,
   rendering, events, HTTP), for both the page runtime (vastra.js, which runs
   <script type="text/vastra"> programs) and programs compiled with
   `vastra build --js`. *)

open Js_of_ocaml
open Vastra
open Value

type Value.opaque += Js of Js.Unsafe.any

let global = Js.Unsafe.global
let document = Dom_html.document
let get obj key = Js.Unsafe.get obj (Js.string key)
let set obj key v = Js.Unsafe.set obj (Js.string key) v
let ctor name args = Ctor (name, args)

let to_js = function
  | Str s -> Js.Unsafe.inject (Js.string s)
  | Int n -> Js.Unsafe.inject (Js.number_of_float (Z.to_float n))
  | Float f -> Js.Unsafe.inject (Js.number_of_float f)
  | Fixed (f, x) -> Js.Unsafe.inject (Js.number_of_float (Z.to_float (Num.to_z f x)))
  | Bool b -> Js.Unsafe.inject (Js.bool b)
  | Opaque (Js v) -> v
  | _ -> Js.Unsafe.inject Js.null

let rec to_json (v : Js.Unsafe.any) =
  let json name args = ctor ("vastra.json/" ^ name) args in
  match Js.to_string (Js.typeof v) with
  | "boolean" -> json "JBool" [ Bool (Js.to_bool (Js.Unsafe.coerce v)) ]
  | "number" -> json "JNumber" [ Float (Js.float_of_number (Js.Unsafe.coerce v)) ]
  | "string" -> json "JString" [ Str (Js.to_string (Js.Unsafe.coerce v)) ]
  | "object" when Js.Opt.test (Js.Opt.return v) && not (Js.Unsafe.equals v Js.null) ->
      if Js.to_bool (Js.Unsafe.fun_call (get (get global "Array") "isArray") [| v |]) then
        let items = Js.to_array (Js.Unsafe.coerce v) in
        json "JArray" [ Vector (Array.map to_json items) ]
      else
        let keys =
          Js.to_array (Js.Unsafe.fun_call (get (get global "Object") "keys") [| v |])
        in
        let entries =
          Array.fold_left
            (fun d k ->
              dict_insert (Str (Js.to_string k)) (to_json (Js.Unsafe.get v k)) d)
            [] keys
        in
        json "JObject" [ Dict entries ]
  | _ -> json "JNull" []

(* Shows an error in the page, above everything else. *)
let show_error text =
  let pre = document##createElement (Js.string "pre") in
  pre##.className := Js.string "vastra-error";
  pre##.textContent := Js.some (Js.string text);
  ignore
    (document##.body##insertBefore (pre :> Dom.node Js.t) document##.body##.firstChild);
  Console.console##error (Js.string text)

let clear_errors () =
  List.iter
    (fun (e : Dom_html.element Js.t) ->
      Js.Opt.iter e##.parentNode (fun p -> ignore (p##removeChild (e :> Dom.node Js.t))))
    (Dom.list_of_nodeList (document##querySelectorAll (Js.string ".vastra-error")))

let guard ~source ~origin f =
  try f () with
  | Diagnostic.Error d -> show_error (Diagnostic.render d source origin)
  | e -> show_error (Diagnostic.render (Diagnostic.bug Diagnostic.nowhere (Printexc.to_string e)) "" "")

(* -- Rendering: Html values to DOM, changing only what differs ------------- *)

let create_text s = (document##createTextNode (Js.string s) :> Dom.node Js.t)

(* Pointer events. The pointer as the program sees it: where, from the
   window's top left, and when, in seconds on the clock of vastra.clock/now. *)
let pointer e =
  let num obj key = Js.float_of_number (Js.Unsafe.coerce (get obj key)) in
  let origin = num (get global "performance") "timeOrigin" in
  Record
    [
      ("x", Float (num e "clientX"));
      ("y", Float (num e "clientY"));
      ("time", Float ((origin +. num e "timeStamp") /. 1000.));
    ]

(* Where a pointer the browser takes over is released: where it was last seen. *)
let last_pointer = ref None

(* At most one move per frame reaches update, the latest; a press or a release
   delivers the waiting move first, so messages keep their order. *)
let waiting_move = ref None

let deliver_move () =
  Option.iter
    (fun deliver ->
      waiting_move := None;
      deliver ())
    !waiting_move

let queue_move deliver =
  if Option.is_none !waiting_move then
    ignore
      (Dom_html.window##requestAnimationFrame
         (Js.wrap_callback (fun _ -> deliver_move ())));
  waiting_move := Some deliver

let set_pointer_handlers el attrs dispatch =
  let handler kind =
    List.find_map
      (function
        | Ctor ("vastra.html/OnPointer", [ Str k; f ]) when k = kind -> Some f | _ -> None)
      attrs
  in
  let down = handler "down" and move = handler "move" and up = handler "up" in
  let send f p = dispatch (fun () -> !apply f [ p ]) in
  let on name f = set el name (Js.wrap_callback f) in
  let main e = Js.float_of_number (Js.Unsafe.coerce (get e "button")) = 0. in
  let seen e =
    let p = pointer e in
    last_pointer := Some p;
    p
  in
  List.iter
    (fun name -> set el name Js.null)
    [ "onpointerdown"; "onpointermove"; "onpointerup"; "onpointercancel" ];
  (* An element that wants moves or the release keeps the pointer it was pressed with. *)
  let capture = Option.is_some move || Option.is_some up in
  if capture || Option.is_some down then
    on "onpointerdown" (fun e ->
        if main e then (
          (if capture then
             try ignore (Js.Unsafe.meth_call el "setPointerCapture" [| get e "pointerId" |])
             with _ -> ());
          deliver_move ();
          let p = seen e in
          Option.iter (fun f -> send f p) down));
  Option.iter
    (fun f ->
      on "onpointermove" (fun e ->
          let p = seen e in
          queue_move (fun () -> send f p)))
    move;
  Option.iter
    (fun f ->
      on "onpointerup" (fun e ->
          if main e then (
            deliver_move ();
            send f (seen e)));
      on "onpointercancel" (fun _ ->
          deliver_move ();
          Option.iter (send f) !last_pointer))
    up

let set_attributes el old_attrs attrs dispatch =
  let name = function
    | Ctor ("vastra.html/Attribute", [ Str n; _ ]) | Ctor ("vastra.html/Flag", [ Str n; _ ])
      ->
        Some n
    | _ -> None
  in
  List.iter
    (fun a ->
      match name a with
      | Some n when not (List.exists (fun b -> name b = Some n) attrs) ->
          el##removeAttribute (Js.string n)
      | _ -> ())
    old_attrs;
  set el "onclick" Js.null;
  set el "oninput" Js.null;
  set el "onsubmit" Js.null;
  List.iter
    (function
      | Ctor ("vastra.html/Attribute", [ Str "value"; Str v ]) ->
          (* The live value, not the attribute; only when it changed, to keep the cursor. *)
          if Js.to_string (get el "value") <> v then set el "value" (Js.string v)
      | Ctor ("vastra.html/Attribute", [ Str n; Str v ]) ->
          el##setAttribute (Js.string n) (Js.string v)
      | Ctor ("vastra.html/Flag", [ Str n; Bool b ]) -> set el n (Js.bool b)
      | Ctor ("vastra.html/OnClick", [ msg ]) ->
          set el "onclick" (Js.wrap_callback (fun _ -> dispatch (fun () -> msg)))
      | Ctor ("vastra.html/OnSubmit", [ msg ]) ->
          (* The message instead of the browser's submission, which would load a page. *)
          set el "onsubmit"
            (Js.wrap_callback (fun e ->
                 ignore (Js.Unsafe.meth_call e "preventDefault" [||]);
                 dispatch (fun () -> msg)))
      | Ctor ("vastra.html/OnInput", [ f ]) ->
          set el "oninput"
            (Js.wrap_callback (fun _ ->
                 dispatch (fun () -> !apply f [ Str (Js.to_string (get el "value")) ])))
      | _ -> ())
    attrs;
  set_pointer_handlers el attrs dispatch

let rec create dispatch v : Dom.node Js.t =
  match v with
  | Ctor ("vastra.html/Text", [ Str s ]) -> create_text s
  | Ctor ("vastra.html/Element", [ Str tag; Vector attrs; Vector children ]) ->
      let el = document##createElement (Js.string tag) in
      set_attributes el [] (Array.to_list attrs) dispatch;
      Array.iter (fun c -> ignore (el##appendChild (create dispatch c))) children;
      (el :> Dom.node Js.t)
  | _ -> (document##createComment (Js.string "nothing") :> Dom.node Js.t)

let rec update dispatch (node : Dom.node Js.t) old v =
  match (old, v) with
  | Ctor ("vastra.html/Text", [ Str a ]), Ctor ("vastra.html/Text", [ Str b ]) ->
      if a <> b then set node "nodeValue" (Js.string b);
      node
  | ( Ctor ("vastra.html/Element", [ Str t1; Vector a1; Vector c1 ]),
      Ctor ("vastra.html/Element", [ Str t2; Vector a2; Vector c2 ]) )
    when t1 = t2 ->
      let el : Dom_html.element Js.t = Js.Unsafe.coerce node in
      set_attributes el (Array.to_list a1) (Array.to_list a2) dispatch;
      let kids = Dom.list_of_nodeList node##.childNodes in
      Array.iteri
        (fun i c ->
          if i < Array.length c1 then (
            let n = List.nth kids i in
            let n' = update dispatch n c1.(i) c in
            if n' != n then ignore (node##replaceChild n' n))
          else ignore (node##appendChild (create dispatch c)))
        c2;
      List.iteri
        (fun i n -> if i >= Array.length c2 then ignore (node##removeChild n))
        kids;
      node
  | Ctor ("vastra.html/Nothing", []), Ctor ("vastra.html/Nothing", []) -> node
  | _ -> create dispatch v

(* -- Views and handlers ---------------------------------------------- *)

(* Whether this runs in a page: a program built with --js may run in Node. *)
let in_page = Js.to_string (Js.typeof (get global "document")) <> "undefined"

(* What each page view shows: its element, and the node and value drawn. *)
let drawn : (string, Dom_html.element Js.t * (Dom.node Js.t * t)) Hashtbl.t =
  Hashtbl.create 4

(* A message from the page goes to the handlers that take it; [heard] lets a
   recording see it first, and drop it while it plays. *)
let heard : (t -> bool) ref = ref (fun _ -> true)

let rec dispatch message =
  guard ~source:"" ~origin:"page" (fun () ->
      let message = message () in
      if !heard message then Value.deliver ~window:false message)

(* Draws each page view into its element, changing only what differs. *)
and draw_views () =
  if in_page then
    guard ~source:"" ~origin:"page" (fun () ->
        List.iter
          (fun (v : Value.view) ->
            match v.place with
            | Str selector -> (
                let tree = !apply v.draw [] in
                match Hashtbl.find_opt drawn selector with
                | Some (root, (node, old)) ->
                    let n = update dispatch node old tree in
                    if n != node then ignore (root##replaceChild n node);
                    Hashtbl.replace drawn selector (root, (n, tree))
                | None -> (
                    let found = document##querySelector (Js.string selector) in
                    match Js.Opt.to_option found with
                    | Some root ->
                        let n = create dispatch tree in
                        ignore (root##appendChild n);
                        Hashtbl.replace drawn selector (root, (n, tree))
                    | None -> show_error ("no element matches the place " ^ selector)))
            | _ -> ())
          !Value.views;
        (* A view the file no longer has stops showing. *)
        Hashtbl.filter_map_inplace
          (fun selector (root, (node, tree)) ->
            let kept (v : Value.view) = v.place = Str selector in
            if List.exists kept !Value.views then
              Some (root, (node, tree))
            else (
              ignore (root##removeChild node);
              None))
          drawn)

(* A change outside a handler is drawn at the next frame, once. *)
let pending = ref false

let schedule () =
  if in_page && not !pending then (
    pending := true;
    ignore
      (Dom_html.window##requestAnimationFrame
         (Js.wrap_callback (fun _ ->
              pending := false;
              draw_views ()))))

(* -- The browser modules' natives ------------------------------------------ *)

let field fields key = List.assoc key fields
let render_all () = draw_views ()

(* -- Recording and replaying ------------------------------------------ *)

let now () = Js.to_float (new%js Js.date_now)##getTime

(* What the page's program is recording or playing: the names the
   file's code changes as they were, by name, and the messages with their time
   from the start in seconds, newest first. *)
type activity = {
  mutable start : (string * t) list;
  mutable messages : (t * float) list;
  began : float;
  playing : bool;
  mutable cancel : unit -> unit;
}

let activity : activity option ref = ref None

(* The names the page's file changes, and their cells, as its session has them. *)
let cells : (unit -> (string * t ref) list) ref = ref (fun () -> [])

let finish a =
  activity := None;
  a.cancel ()

let recording a =
  let message (msg, at) = Record [ ("msg", msg); ("at", Float at) ] in
  let messages = Vector (Array.of_list (List.rev_map message a.messages)) in
  Record [ ("start", Record a.start); ("messages", messages) ]

(* A message from the page, while recording, up to 30 seconds. While a replay
   plays, the page's input is dropped. *)
let hear msg =
  match !activity with
  | Some a when a.playing -> false
  | Some a ->
      let at = (now () -. a.began) /. 1000. in
      if at <= 30. then a.messages <- (msg, at) :: a.messages;
      true
  | None -> true

(* While a loop plays, a set! that isn't the loop's changes its start too. *)
let delivering = ref false

let assigned cell =
  match !activity with
  | Some a when a.playing && not !delivering ->
      List.iter
        (fun (name, c) ->
          if c == cell then
            a.start <- List.map (fun (n, v) -> (n, if n = name then !c else v)) a.start)
        (!cells ())
  | _ -> ()

let failure name k = k (Error (ctor ("vastra.browser/" ^ name) []))

let record =
  Task
    (fun k ->
      Option.iter finish !activity;
      let start = List.map (fun (n, c) -> (n, !c)) (!cells ()) in
      activity :=
        Some { start; messages = []; began = now (); playing = false; cancel = ignore };
      k (Ok Unit))

let stop =
  Task
    (fun k ->
      match !activity with
      | Some a ->
          finish a;
          k (Ok (recording a))
      | None -> failure "NotRecording" k)

(* One message at a time, each timer set when the last fires: a tab the browser
   slows down plays slower, and never in a burst. A replay stopped while it
   plays stops. *)
let play ~looping = function
  | [ Record recorded ] ->
      let message = function
        | Record m ->
            (field m "msg", match field m "at" with Float s -> s | _ -> 0.)
        | _ -> raise (Internal "a recorded message")
      in
      let messages =
        match field recorded "messages" with
        | Vector ms -> List.rev_map message (Array.to_list ms)
        | _ -> raise (Internal "a recording's messages")
      in
      let start =
        match field recorded "start" with Record f -> f | _ -> raise (Internal "a start")
      in
      let run k =
        Option.iter finish !activity;
        let a = { start; messages; began = now (); playing = true; cancel = ignore } in
        activity := Some a;
        let timer = ref None in
        let after seconds f = timer := Some (Dom_html.setTimeout f (seconds *. 1000.)) in
        let deliver msg =
          guard ~source:"" ~origin:"page" (fun () ->
              delivering := true;
              Fun.protect
                ~finally:(fun () -> delivering := false)
                (fun () -> Value.deliver ~window:false msg))
        in
        let rec turn () =
          List.iter
            (fun (n, c) -> Option.iter (fun v -> c := v) (List.assoc_opt n a.start))
            (!cells ());
          draw_views ();
          next 0. (List.rev a.messages)
        and next last = function
          | (msg, at) :: rest ->
              after (at -. last) (fun () ->
                  deliver msg;
                  next at rest)
          | [] -> if looping then after 1. turn else finish a
        in
        (* A press or a key on the page stops it, before the page hears it. *)
        let listen name =
          Dom_html.addEventListener Dom_html.window (Dom_html.Event.make name)
            (Dom_html.handler (fun _ ->
                 finish a;
                 Js._true))
            Js._true
        in
        let listeners = [ listen "pointerdown"; listen "keydown" ] in
        a.cancel <-
          (fun () ->
            Option.iter Dom_html.clearTimeout !timer;
            List.iter Dom_html.removeEventListener listeners;
            if not looping then k (Ok Unit));
        turn ();
        fun () -> finish a
      in
      Task
        (fun k ->
          if looping then (
            let _cancel = run ignore in
            k (Ok Unit))
          else wait run k)
  | _ -> raise (Internal "browser/replay")

let unreachable k why = k (Error (ctor "vastra.http/NetworkError" [ Str why ]))

(* What a request gives [k]: the answer, an http/Answer, unless its
   status is outside 200-299. *)
let answered k status headers body =
  let answer =
    Record
      [ ("status", Int (Z.of_int status)); ("headers", Dict headers); ("body", Str body) ]
  in
  if status >= 200 && status < 300 then k (Ok answer)
  else k (Error (ctor "vastra.http/BadStatus" [ Int (Z.of_int status); answer ]))

(* A GET in a page; stopped while it waits, it is aborted. *)
let request_in_page url k =
  let xhr = XmlHttpRequest.create () in
  xhr##_open (Js.string "GET") (Js.string url) Js._true;
  xhr##.onreadystatechange :=
    Js.wrap_callback (fun () ->
        if xhr##.readyState = XmlHttpRequest.DONE then
          guard ~source:"" ~origin:"page" (fun () ->
              let header line =
                match String.index_opt line ':' with
                | Some i ->
                    let name = String.lowercase_ascii (String.sub line 0 i) in
                    let value = String.sub line (i + 1) (String.length line - i - 1) in
                    Some (Str name, Str (String.trim value))
                | None -> None
              in
              let all = Js.to_string xhr##getAllResponseHeaders in
              let headers =
                List.fold_left (fun d (n, v) -> dict_insert n v d) []
                  (List.filter_map header (String.split_on_char '\n' all))
              in
              let body = Js.Opt.case xhr##.responseText (fun () -> "") Js.to_string in
              if xhr##.status = 0 then unreachable k ("cannot reach " ^ url)
              else answered k xhr##.status headers body));
  xhr##send Js.null;
  fun () -> xhr##abort

(* The same in Node, which has fetch instead. A header's get joins its values
   with ", ", Set-Cookie's too. A URL has no page to be read against there. *)
let request_in_node url k =
  let inject = Js.Unsafe.inject in
  let address = inject (Js.string url) and text s = Str (Js.to_string s) in
  let controller = Js.Unsafe.new_obj (get global "AbortController") [||] in
  let failed _ =
    let whole = Js.Unsafe.meth_call (get global "URL") "canParse" [| address |] in
    let why = ": outside a page, a URL starts with http://" in
    unreachable k ("cannot reach " ^ url ^ if Js.to_bool whole then "" else why)
  in
  let next promise f =
    Js.Unsafe.meth_call promise "then"
      [| inject (Js.wrap_callback f); inject (Js.wrap_callback failed) |]
  in
  let options = Js.Unsafe.obj [| ("signal", get controller "signal") |] in
  let fetched = Js.Unsafe.fun_call (get global "fetch") [| address; options |] in
  ignore
    (next fetched (fun response ->
         let all = get response "headers" and headers = ref [] in
         let add _ name _ =
           let value = Js.Unsafe.meth_call all "get" [| inject name |] in
           headers := dict_insert (text name) (text value) !headers
         in
         ignore (Js.Unsafe.meth_call all "forEach" [| inject (Js.wrap_callback add) |]);
         let status = int_of_float (Js.float_of_number (get response "status")) in
         ignore
           (next (Js.Unsafe.meth_call response "text" [||]) (fun body ->
                answered k status !headers (Js.to_string body)))));
  fun () -> ignore (Js.Unsafe.meth_call controller "abort" [||])

let request url =
  if Js.Optdef.test (get global "XMLHttpRequest") then request_in_page url
  else request_in_node url

let body_of = function Record fields -> List.assoc "body" fields | _ -> Unit

let get_text = function
  | [ Str url ] -> Task (wait (fun k -> request url (fun r -> k (Result.map body_of r))))
  | _ -> raise (Internal "http/get-text")

(* Told a written type, the body is decoded to it: a body that isn't
   JSON and JSON of the wrong shape are both BadBody. *)
let get_answer = function
  | [ Str url ] -> Task (wait (request url))
  | [ Opaque (Json.Shape shape); Str url ] ->
      let decoded answer =
        let bad why = Error (ctor "vastra.http/BadBody" [ Str why ]) in
        match Json.parse (Value.to_display (body_of answer)) with
        | Ctor ("Ok", [ j ]) -> (
            match Json.decode shape j with
            | Ctor ("Ok", [ v ]) -> Ok v
            | Ctor (_, [ Str why ]) -> bad why
            | _ -> raise (Internal "http/get"))
        | Ctor (_, [ Str why ]) -> bad ("not JSON: " ^ why)
        | _ -> raise (Internal "http/get")
      in
      Task (wait (fun k -> request url (fun r -> k (Result.bind r decoded))))
  | _ -> raise (Internal "http/get")

(* -- JavaScript from any program --------------------------------------- *)

(* A value that can't go to JavaScript, and why: the call given it fails. *)
type Value.opaque += Refused of string

exception Refused_value of string

(* A value going to JavaScript, by the rules js/value states. *)
let rec encode v : Js.Unsafe.any =
  let refuse why = raise (Refused_value why) in
  let key k = if Util.may_miss k then String.sub k 0 (String.length k - 1) else k in
  let obj entries = Js.Unsafe.obj (Array.of_list entries) in
  match v with
  | Str _ | Int _ | Float _ | Fixed _ | Bool _ | Opaque (Js _) -> to_js v
  | Opaque (Refused why) -> refuse why
  | Unit -> Js.Unsafe.inject Js.undefined
  | Vector items | Buffer items -> Js.Unsafe.inject (Js.array (Array.map encode items))
  | Record fields -> obj (List.map (fun (k, x) -> (key k, encode x)) fields)
  | Dict entries ->
      let entry = function
        | Str k, x -> (k, encode x)
        | _ -> refuse "a Dict not keyed by text"
      in
      obj (List.map entry entries)
  | Ctor ("None", []) -> Js.Unsafe.inject Js.null
  | Ctor ("Some", [ x ]) -> encode x
  | Ctor (name, []) when Hashtbl.mem Value.words name ->
      Js.Unsafe.inject (Js.string (Hashtbl.find Value.words name))
  | Ctor (name, []) -> refuse (unqualified name ^ ", which has no outside word")
  | Ctor (name, _) -> refuse (unqualified name ^ ", which holds values")
  | Closure _ | Builtin _ | Global _ | Generic _ ->
      refuse "a function: give it with js/callback"
  | _ -> refuse "this value"

let fails name args = Error (ctor ("vastra.js/" ^ name) args)

(* An exception, or what a Promise was rejected with: its name and message. *)
let thrown (reason : Js.Unsafe.any) =
  let describe =
    Js.Unsafe.js_expr
      "(function(r){return r instanceof Error?[r.name, r.message]:['Error', String(r)]})"
  in
  let parts = Js.Unsafe.fun_call describe [| reason |] in
  let part p = Str (Js.to_string p) in
  fails "Thrown" (List.map part (Array.to_list (Js.to_array parts)))

let has (owner : Js.Unsafe.any) key =
  let has = Js.Unsafe.js_expr "(function(o,k){return o != null && k in Object(o)})" in
  Js.to_bool (Js.Unsafe.fun_call has [| owner; Js.Unsafe.inject (Js.string key) |])

let is_promise (v : Js.Unsafe.any) =
  let thenable =
    Js.Unsafe.js_expr "(function(v){return v != null && typeof v.then === 'function'})"
  in
  Js.to_bool (Js.Unsafe.fun_call thenable [| v |])

(* What a type reads of a JavaScript value, as Json: only the properties it
   names, so an event or an element is never walked whole (it may hold
   itself), and a property its prototype gives, such as an event's key, is
   read too. An undefined property is a missing key. *)
let rec read_as (shape : Shape.t) (v : Js.Unsafe.any) =
  let is f x = Js.to_bool (Js.Unsafe.fun_call f [| x |]) in
  let missing = is (Js.Unsafe.js_expr "(function(v){return v == null})") in
  let undefined = Js.Unsafe.js_expr "(function(v){return v === undefined})" in
  let an_object = Js.Unsafe.js_expr "(function(v){return typeof v === 'object'})" in
  let an_array = get (get global "Array") "isArray" in
  match shape with
  | Record keys when is an_object v && not (missing v || is an_array v) ->
      let field d (k, s) =
        let name = if Util.may_miss k then String.sub k 0 (String.length k - 1) else k in
        let x = get v name in
        if is undefined x then d else dict_insert (Str name) (read_as s x) d
      in
      ctor "vastra.json/JObject" [ Dict (List.fold_left field [] keys) ]
  | Vector s when is an_array v ->
      let items = Js.to_array (Js.Unsafe.coerce v) in
      ctor "vastra.json/JArray" [ Vector (Array.map (read_as s) items) ]
  | Option s when not (missing v) -> read_as s v
  | _ -> to_json v

(* What a call gives, as the type its let was told, or a Value. *)
let decoded told (v : Js.Unsafe.any) =
  match told with
  | None -> Ok (Opaque (Js v))
  | Some shape -> (
      match Json.decode shape (Opaque (Js v)) with
      | Ctor ("Ok", [ x ]) -> Ok x
      | Ctor (_, [ Str why ]) -> fails "BadValue" [ Str why ]
      | _ -> raise (Internal "vastra.js: decoding"))

(* A task that runs [act], a JavaScript call, and gives what [give] makes of
   its answer. A Promise is waited for, though it can't be called off. *)
let js_task ?(give = decoded) told act =
  Task
    (fun k ->
      match act () with
      | Ok v when is_promise v ->
          let settled f = Js.Unsafe.inject (Js.wrap_callback f) in
          let start ended =
            let kept x = ended (give told x) and rejected r = ended (thrown r) in
            ignore (Js.Unsafe.meth_call v "then" [| settled kept; settled rejected |]);
            ignore
          in
          wait start k
      | Ok v -> k (give told v)
      | Error _ as e -> k e
      | exception Js_error.Exn e -> k (thrown (Js.Unsafe.inject (Js_error.to_error e)))
      | exception Refused_value why -> k (fails "BadArgument" [ Str why ]))

(* Runs [f] as a handler: a task it gives runs too, then what it sent, and
   the views are drawn again. Gives what it gives, unless a task. *)
let as_handler f args =
  let given = ref None in
  let run () =
    (match !apply f args with
    | Task t -> t (fun _ -> handle_sent (); !redraw ())
    | v -> given := Some v);
    handle_sent ();
    !redraw ()
  in
  if in_page then guard ~source:"" ~origin:"page" run else run ();
  !given

let arguments n (args : Js.Unsafe.any_js_array) = List.init n (Js.Unsafe.get args)

(* It answers JavaScript with what it gives. *)
let callback n f =
  let called args =
    let as_js v = try encode v with Refused_value _ -> Js.Unsafe.inject Js.undefined in
    let given = as_handler f (List.map (fun v -> Opaque (Js v)) (arguments n args)) in
    Option.fold ~none:(Js.Unsafe.inject Js.undefined) ~some:as_js given
  in
  Opaque (Js (Js.Unsafe.inject (Js.Unsafe.callback_with_arguments called)))

let short ctor = List.hd (List.rev (String.split_on_char '/' ctor))

exception Misfit of string

(* A message JavaScript sent, its values decoded now. On the next turn, as
   send! has it, it is handled as the page's are; or [misfit] runs, with why. *)
let sent (ctor, shapes) misfit values =
  let value i shape =
    let missing = Js.Unsafe.inject Js.undefined in
    let v = Option.value (List.nth_opt values i) ~default:missing in
    match Json.decode shape (Opaque (Js v)) with
    | Ctor ("Ok", [ x ]) -> x
    | Ctor (_, [ Str why ]) when List.length shapes = 1 -> raise (Misfit why)
    | Ctor (_, [ Str why ]) -> raise (Misfit (Printf.sprintf "value %d: %s" (i + 1) why))
    | _ -> raise (Internal "vastra.js: a message's value")
  in
  let handle =
    match Ctor (ctor, List.mapi value shapes) with
    | m when in_page -> fun () -> dispatch (fun () -> m)
    | m -> fun () -> Value.deliver ~window:false m
    | exception Misfit why ->
        fun () -> ignore (as_handler misfit [ Str (short ctor ^ ": " ^ why) ])
  in
  let _cancel = !Clock.after 0. handle in
  ()

(* What vastra.send may send, once js/receive opens it. *)
let receiving = ref None

let throw message =
  let error = Js.Unsafe.js_expr "(function(m){throw new Error(m)})" in
  Js.Unsafe.fun_call error [| Js.Unsafe.inject (Js.string message) |]

(* JavaScript's vastra.send(name, ...values). A message the program doesn't
   have is JavaScript's to handle. *)
let send (args : Js.Unsafe.any_js_array) =
  let all = arguments (Js.Unsafe.get args "length") args in
  match (!receiving, all) with
  | None, _ ->
      throw "this program takes no messages from JavaScript: js/receive opens them"
  | Some (ctors, misfit), name :: values -> (
      let name = Js.to_string (Js.Unsafe.fun_call (get global "String") [| name |]) in
      match List.find_opt (fun (ctor, _) -> short ctor = name) ctors with
      | Some message -> sent message misfit values
      | None ->
          let names = String.concat ", " (List.map (fun (ctor, _) -> short ctor) ctors) in
          throw (Printf.sprintf "no message %s; the program takes %s" name names))
  | Some _, [] -> throw "vastra.send takes a message's name, then its values"

let js_natives =
  let native name run = ("vastra.js/" ^ name, Builtin { builtin_name = name; run }) in
  (* A native told a type gets it first. *)
  let told f = function
    | Opaque (Json.Shape s) :: args -> f (Some s) args
    | args -> f None args
  in
  let found owner what key =
    if has owner key then Ok (get owner key)
    else fails "Missing" [ Str (what ^ " " ^ key) ]
  in
  let values = function Vector xs -> Array.map encode xs | _ -> [||] in
  let wrong name = raise (Internal ("vastra.js/" ^ name)) in
  [
    native "global"
      (told (fun t -> function
         | [ Str name ] ->
             js_task t (fun () -> found (Js.Unsafe.inject global) "global" name)
         | _ -> wrong "global"));
    native "get"
      (told (fun t -> function
         | [ Opaque (Js o); Str key ] -> js_task t (fun () -> found o "property" key)
         | _ -> wrong "get"));
    native "call*"
      (told (fun t -> function
         | [ Opaque (Js f); xs ] ->
             js_task t (fun () -> Ok (Js.Unsafe.fun_call f (values xs)))
         | _ -> wrong "call*"));
    native "method*"
      (told (fun t -> function
         | [ Opaque (Js o); Str name; xs ] ->
             js_task t (fun () ->
                 Result.map
                   (fun _ -> Js.Unsafe.meth_call o name (values xs))
                   (found o "method" name))
         | _ -> wrong "method*"));
    native "new*"
      (told (fun t -> function
         | [ Opaque (Js c); xs ] ->
             js_task t (fun () -> Ok (Js.Unsafe.new_obj c (values xs)))
         | _ -> wrong "new*"));
    native "set" (function
      | [ Opaque (Js o); Str key; v ] ->
          js_task ~give:(fun _ _ -> Ok Unit) None (fun () ->
              set o key (encode v);
              Ok (Js.Unsafe.inject Js.undefined))
      | _ -> wrong "set");
    native "value" (function
      | [ v ] -> (
          try Opaque (Js (encode v)) with Refused_value why -> Opaque (Refused why))
      | _ -> wrong "value");
    native "reply" (function [ v ] -> v | _ -> wrong "reply");
    native "callback*" (function
      | [ Int n; f ] -> callback (Z.to_int n) f
      | _ -> wrong "callback*");
    native "message*" (function
      | [ Opaque (Json.Shape (Message [ (_, shapes) as message ])); _; misfit ] ->
          let called args = sent message misfit (arguments (List.length shapes) args) in
          Opaque (Js (Js.Unsafe.inject (Js.Unsafe.callback_with_arguments called)))
      | _ -> wrong "message*");
    native "receive*" (function
      | [ Opaque (Json.Shape (Message ctors)); _; misfit ] ->
          receiving := Some (ctors, misfit);
          Unit
      | _ -> wrong "receive*");
  ]

(* -- The clock -------------------------------------------------------- *)

(* The platform's timers, in a page or in Node. A wait longer than 2^31 - 1
   milliseconds fires at once there, so it is several. *)
let after seconds f =
  let timer = ref (Js.Unsafe.inject 0) in
  let rec wait ms =
    let part = Float.min ms 2147483647. in
    let fire () = if ms > part then wait (ms -. part) else f () in
    timer :=
      Js.Unsafe.fun_call (get global "setTimeout")
        [| Js.Unsafe.inject (Js.wrap_callback fire); Js.Unsafe.inject part |]
  in
  wait (seconds *. 1000.);
  fun () -> ignore (Js.Unsafe.fun_call (get global "clearTimeout") [| !timer |])

let elapsed () =
  Js.float_of_number (Js.Unsafe.meth_call (get global "performance") "now" [||]) /. 1000.

(* A file of the page's program, read synchronously, so that a module loads
   at its require as it does from a disk. *)
let load url =
  let xhr = XmlHttpRequest.create () in
  xhr##_open (Js.string "GET") (Js.string url) Js._false;
  xhr##send Js.null;
  (xhr##.status, Js.Opt.case xhr##.responseText (fun () -> "") Js.to_string)

let read url = snd (load url)

(* -- ES modules ---------------------------------------------------------- *)

(* The ES modules the program imports, by what it wrote, loaded before it
   runs: each one's default export if it has one, else the module. *)
let modules : (string, Js.Unsafe.any) Hashtbl.t = Hashtbl.create 4

let imported spec = Opaque (Js (Hashtbl.find modules spec))

(* Where a page finds a module: beside the page, as its Vastra modules are,
   or a package in the node_modules there, by its package.json. Node
   finds them itself, from the program's file. *)
let address spec =
  let url s =
    let base = Js.Unsafe.inject (get document "baseURI") in
    let s = Js.Unsafe.inject (Js.string s) in
    let whole = Js.Unsafe.new_obj (get global "URL") [| s; base |] in
    Js.to_string (get whole "href")
  in
  let package =
    match String.split_on_char '/' spec with
    | scope :: name :: _ when String.starts_with ~prefix:"@" scope -> scope ^ "/" ^ name
    | name :: _ -> name
    | [] -> spec
  in
  let entry =
    Js.Unsafe.js_expr
      "(function(t){var p;try{p=JSON.parse(t)}catch(_){return 'index.js'}\
       var e=p.exports;if(e&&typeof e==='object'&&'.' in e)e=e['.'];\
       while(e&&typeof e==='object')e=e.browser||e.import||e.default;\
       return typeof e==='string'?e:(p.module||p.main||'index.js')})"
  in
  if not in_page then spec
  else if String.starts_with ~prefix:"." spec || String.starts_with ~prefix:"/" spec
          || String.contains spec ':' then url spec
  else if package <> spec then url ("node_modules/" ^ spec)
  else
    let manifest = read (url ("node_modules/" ^ package ^ "/package.json")) in
    let file = Js.Unsafe.fun_call entry [| Js.Unsafe.inject (Js.string manifest) |] in
    url ("node_modules/" ^ package ^ "/" ^ Js.to_string file)

(* Loads the modules [specs] names that aren't loaded yet, then calls [k]. A
   module that can't be loaded is shown, and [k] isn't called. *)
let preload specs k =
  let missing = List.filter (fun s -> not (Hashtbl.mem modules s)) specs in
  let missing = List.sort_uniq String.compare missing in
  let load =
    Js.Unsafe.js_expr
      "(function(s,a){return import(a).then(\
       function(m){return m.default!==undefined?m.default:m},\
       function(e){throw new Error('cannot import '+s+': '+e.message)})})"
  in
  let all = Js.Unsafe.js_expr "(function(ps){return Promise.all(ps)})" in
  let text s = Js.Unsafe.inject (Js.string s) in
  let loading s = Js.Unsafe.fun_call load [| text s; text (address s) |] in
  let loaded found =
    List.iteri (fun i s -> Hashtbl.replace modules s (Js.Unsafe.get found i)) missing;
    k ()
  in
  let failed reason =
    let message = Js.to_string (get reason "message") in
    if in_page then show_error message
    else (
      prerr_endline message;
      exit 1)
  in
  if missing = [] then k ()
  else
    let promises = Js.array (Array.of_list (List.map loading missing)) in
    let promise = Js.Unsafe.fun_call all [| Js.Unsafe.inject promises |] in
    let callback f = Js.Unsafe.inject (Js.wrap_callback f) in
    ignore (Js.Unsafe.meth_call promise "then" [| callback loaded; callback failed |])

(* Provides the browser natives. *)
let install () =
  (Json.of_opaque :=
     fun shape -> function Js v -> read_as shape v | _ -> raise (Internal "not data"));
  Value.redraw := draw_views;
  (Value.changed :=
     fun cell ->
       schedule ();
       assigned cell);
  heard := hear;
  Clock.after := after;
  Clock.elapsed := elapsed;
  Builtins.extra :=
    js_natives
    @ [
      ("vastra.browser/record", record);
      ("vastra.browser/stop", stop);
      ( "vastra.browser/replay",
        Builtin { builtin_name = "replay"; run = play ~looping:false } );
      ( "vastra.browser/loop",
        Builtin { builtin_name = "loop"; run = play ~looping:true } );
      ("vastra.http/get-text", Builtin { builtin_name = "get-text"; run = get_text });
      ("vastra.http/get", Builtin { builtin_name = "get"; run = get_answer });
      ( "vastra.js/to-json",
        Builtin
          {
            builtin_name = "to-json";
            run =
              (function
              | [ Opaque (Js v) ] -> to_json v
              | _ -> to_json (Js.Unsafe.inject Js.null));
          } );
    ]
