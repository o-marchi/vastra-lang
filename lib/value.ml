module Env = Map.Make (String)

(* Platforms extend this with their own values (the browser runtime adds JavaScript values). *)
type opaque = ..

type t =
  | Int of Z.t
  | Float of float
  | Fixed of Num.fixed * int32 (* U8 to I32, as Num.wrap keeps them *)
  | Bool of bool
  | Str of string
  | Unit
  | Vector of t array (* never mutated *)
  | Buffer of t array (* a vector that one name holds, changed in place *)
  | Dict of (t * t) list (* sorted by key *)
  | Record of (string * t) list
  | Ctor of string * t list
  | Keyword of string (* as a function: reads that key *)
  | Form of Reader.node (* code as data, keeping where it came from *)
  | Opaque of opaque (* a value of the host platform, such as a JavaScript object *)
  | Task of (((t, t) result -> unit) -> unit)
    (* work to do, run only when asked; it calls back with the result, maybe later *)
  | Closure of closure
  | Builtin of builtin
  | Generic of (Num.t list -> t)
    (* a function generic over number, waiting for the types it is used at *)
  | Told of Num.t (* a local holding a type a generic function was told *)
  | Global of t ref * Num.t list
    (* a global function used as a value: its cell, and the number types it is
       used at. Calls run the cell's current definition, whose type never
       changes. *)
  | Running of running (* a task later started, which stop! stops *)

(* [name] is set by def/defn: the function can call itself by it. Closures do
   not capture global names: those are looked up when used (late binding), in
   the globals of the session that made the closure. *)
and closure = {
  name : string option;
  lambda : Ast.lambda;
  locals : (string * t) list;
  globals : t ref Env.t ref;
  source : (string * string) option; (* the origin and text its code was read from *)
}

(* Arguments are guaranteed by the type checker. *)
and builtin = { builtin_name : string; run : t list -> t }

(* A running task: what it waits for, by number, each with what calls it
   off, so that stopping it calls them off and a wait that ends is forgotten. *)
and running = { mutable stopped : bool; waits : (int, unit -> unit) Hashtbl.t }


(* Raised by built-ins that receive values the type checker should have ruled out. *)
exception Internal of string

(* A function generic over number, at the types it is used at; any other value
   is itself. *)
let at v types = match v with Generic f -> f types | v -> v

(* A whole number written in the code, as a value of its type. *)
let literal (t : Num.t) n =
  match t with Int -> Int n | Float -> Float (Z.to_float n) | Fixed f -> Fixed (f, Num.of_z f n)

(* Is [v], a whole number of any type, [n]? For literal patterns. *)
let is_whole n = function
  | Int x -> Z.equal x n
  | Fixed (f, x) -> Z.equal (Num.to_z f x) n
  | _ -> false

(* While a macro runs: its name and where it is used. Code the macro builds
   gets this location, so errors in an expansion point at the use. *)
let site : (string * Reader.span) option ref = ref None
let gensyms = ref 0

(* [node]'s forms, all located at the current site (if a macro is running). *)
let rec at_site (node : Reader.node) =
  match !site with
  | None -> node
  | Some (name, span) ->
      let form : Reader.form =
        match node.form with
        | List items -> List (List.map at_site items)
        | Vector items -> Vector (List.map at_site items)
        | Map entries -> Map (List.map (fun (k, v) -> (at_site k, at_site v)) entries)
        | f -> f
      in
      { form; span; origin = Some name }

(* A new node made by the running macro; [inner] forms keep their own locations. *)
let made ?(default = { Reader.start = 0; stop = 0 }) form =
  match !site with
  | Some (name, span) -> { Reader.form; span; origin = Some name }
  | None -> { Reader.form; span = default; origin = None }

(* Each constructor's outside word, by its qualified name, for values
   going outside as data. *)
let words : (string, string) Hashtbl.t = Hashtbl.create 16

(* The cells set! changed in the submission running, with what they held, so
   a failed one puts them back. *)
let assigned : (t ref * t) list option ref = ref None

(* The handlers and views of the programs running, which a runtime (a
   page, a window) runs. A handler gives, for an event, the function running
   its body if it takes the event; [window]: whether it takes window events,
   else the page's messages. A view draws its place, a selector or a window.
   [from]: the file that wrote it, or None for the prompt. *)
type handler = { from : string option; window : bool; handle : t }
type view = { at : string option; place : t; draw : t }

let handlers : handler list ref = ref []
let views : view list ref = ref []

(* Set by a runtime: draws the views again, after a change. [changed]
   is told of each set!, so a change no handler made, in a task's last part
   or at the prompt, is drawn too. *)
let redraw : (unit -> unit) ref = ref ignore
let changed : (t ref -> unit) ref = ref ignore

(* Set by vastra.window when it opens one: runs its frames until it closes,
   after the file that opened it has run. *)
let loop : (unit -> unit) ref = ref ignore

(* The same place: a selector, or the same window. *)
let same_place a b = match (a, b) with Str x, Str y -> x = y | _ -> a == b


(* Set by the evaluator, so built-ins can call functions they are given. *)
let apply : (t -> t list -> t) ref = ref (fun _ _ -> raise (Internal "apply is not set"))

(* The messages send! gave, which wait for the handler running to end. *)
let outbox : t Queue.t = Queue.create ()

(* Gives [event] to the first handler that takes it, as one match does, and
   runs what it gives: a value, or a task, which cannot fail. Then the
   messages it sent; the views are drawn again after each. *)
let rec deliver ~window event =
  let taker (h : handler) =
    if h.window <> window then None
    else
      match !apply h.handle [ event ] with Ctor ("Some", [ run ]) -> Some run | _ -> None
  in
  (match List.find_map taker !handlers with
  | Some run -> (
      match !apply run [] with
      | Task t ->
          t (fun _ ->
              handle_sent ();
              !redraw ())
      | _ -> ())
  | None -> ());
  handle_sent ();
  !redraw ()

and handle_sent () =
  match Queue.take_opt outbox with Some m -> deliver ~window:false m | None -> ()

(* A message sent while no handler runs is handled on the next turn. *)
let send message =
  Queue.push message outbox;
  let _cancel = !Clock.after 0. handle_sent in
  ()

let running () = { stopped = false; waits = Hashtbl.create 1 }

(* The running whose code runs now: the program's, which never stops, unless
   later, task/race or task/first-of started one. *)
let program = running ()
let current = ref program

let within r f =
  let outer = !current in
  current := r;
  Fun.protect ~finally:(fun () -> current := outer) f

let numbered = ref 0

(* [cancel] calls off something [r] waits for; what this gives forgets it. *)
let waiting r cancel =
  incr numbered;
  let n = !numbered in
  Hashtbl.replace r.waits n cancel;
  fun () -> Hashtbl.remove r.waits n

(* Stopping one that has ended, or stopped, does nothing. *)
let stop r =
  if not r.stopped then (
    r.stopped <- true;
    let cancels = List.of_seq (Hashtbl.to_seq_values r.waits) in
    Hashtbl.reset r.waits;
    List.iter (fun cancel -> cancel ()) cancels)

(* A wait for something outside the program, where a task can stop:
   [start] begins it, given what to call when it ends, and gives what calls it
   off. The task goes on with [k] in the running it was in, unless that one
   was stopped meanwhile. *)
let wait start k =
  let r = !current and forget = ref ignore in
  let ended outcome =
    !forget ();
    if not r.stopped then within r (fun () -> k outcome)
  in
  forget := waiting r (start ended)

let escape s =
  String.concat ""
    (List.map
       (function
         | '"' -> "\\\""
         | '\\' -> "\\\\"
         | '\n' -> "\\n"
         | '\t' -> "\\t"
         | c -> String.make 1 c)
       (List.of_seq (String.to_seq s)))

(* What a program prints shows a constructor as its module wrote it, wherever
   it is printed. *)
let unqualified n =
  match String.rindex_opt n '/' with
  | Some i -> String.sub n (i + 1) (String.length n - i - 1)
  | None -> n

(* As code: strings quoted. The REPL and errors give [name], which shows a
   qualified name as typed where it is shown, and a [width] to lay it out for. *)
let rec to_doc ?name v : Pretty.t =
  let doc = to_doc ?name in
  let fn n = match name with Some f -> f n | None -> n in
  let group opening items sep closing = Pretty.Group { opening; items; sep; closing } in
  let text s = Pretty.Text s in
  match v with
  | Int n -> text (Z.to_string n)
  | Fixed (f, x) -> text (Z.to_string (Num.to_z f x))
  | Float f -> text (Util.float_to_string f)
  | Bool b -> text (string_of_bool b)
  | Str s -> text ("\"" ^ escape s ^ "\"")
  | Unit -> text "unit"
  | Vector items | Buffer items -> group "[" (Array.to_list (Array.map doc items)) " " "]"
  | Dict entries ->
      let entry (k, v) = group "" [ doc k; doc v ] " " "" in
      group "{" (List.map entry entries) ", " "}"
  | Record fields ->
      let field (k, v) = group (":" ^ k ^ " ") [ doc v ] "" "" in
      group "{" (List.map field fields) ", " "}"
  | Ctor (c, args) -> (
      let c = match name with Some f -> f c | None -> unqualified c in
      match args with
      | [] -> text c
      | _ -> group ("(" ^ c ^ " ") (List.map doc args) " " ")")
  | Keyword k -> text (":" ^ k)
  | Form n -> text ("'" ^ Reader.to_source n)
  | Task _ -> text "#<task>"
  | Opaque _ -> text "#<opaque>"
  | Closure { name = Some n; _ } -> text ("#<fn " ^ fn n ^ ">")
  | Closure { name = None; _ } -> text "#<fn>"
  | Builtin { builtin_name = ""; _ } -> text "#<fn>"
  | Builtin b -> text ("#<fn " ^ fn b.builtin_name ^ ">")
  | Generic _ -> text "#<fn>"
  | Told _ -> text "#<type>"
  | Running _ -> text "#<running>"
  | Global (cell, types) -> doc (at !cell types)

let to_string ?name ?width v = Pretty.render ?width (to_doc ?name v)

(* Whether [to_string] gives code that reads back as this value. A Dict prints
   as a map, which the reader does not take with keys that are not keywords. *)
let rec is_code = function
  | Int _ | Fixed _ | Bool _ | Str _ | Unit | Keyword _ | Form _ -> true
  | Float f -> Float.is_finite f
  | Vector items | Buffer items -> Array.for_all is_code items
  | Record fields -> List.for_all (fun (_, v) -> is_code v) fields
  | Ctor (_, args) -> List.for_all is_code args
  | Dict _ | Opaque _ | Task _ | Closure _ | Builtin _ | Generic _ | Told _ | Global _
  | Running _ ->
      false

(* A buffer the prompt gives back is kept as a vector. *)
let rec frozen = function
  | Buffer items -> Vector items
  | Record fields -> Record (List.map (fun (k, v) -> (k, frozen v)) fields)
  | Ctor (c, args) -> Ctor (c, List.map frozen args)
  | v -> v

(* As text, for str: strings as they are. *)
let to_display = function Str s -> s | v -> to_string v

(* Structural equality on equatable values; floats follow IEEE (NaN ≠ NaN). *)
let rec equal a b =
  match (a, b) with
  | Int x, Int y -> Z.equal x y
  | Float x, Float y -> x = y
  | Vector x, Vector y -> Array.length x = Array.length y && Array.for_all2 equal x y
  | Dict x, Dict y ->
      List.length x = List.length y
      && List.for_all2 (fun (k, v) (k', v') -> equal k k' && equal v v') x y
  | Record x, Record y ->
      (* Same type means same keys, possibly in another order, but for those
         that may be missing. *)
      List.length x = List.length y
      && List.for_all
           (fun (k, v) -> Option.fold (List.assoc_opt k y) ~none:false ~some:(equal v))
           x
  | Ctor (c, x), Ctor (d, y) -> c = d && List.for_all2 equal x y
  | x, y -> x = y

(* A total order on comparable values, for sorting and dictionary keys. *)
let compare a b =
  match (a, b) with
  | Int x, Int y -> Z.compare x y
  | Fixed (f, x), Fixed (_, y) -> Num.compare f x y
  | Float x, Float y -> Float.compare x y
  | Str x, Str y -> String.compare x y
  | _ -> raise (Internal "comparing values that are not comparable")

(* Dictionary entries stay sorted by key. *)
let rec dict_insert k v = function
  | [] -> [ (k, v) ]
  | (k', _) :: rest when compare k k' = 0 -> (k, v) :: rest
  | (k', v') :: rest when compare k k' < 0 -> (k, v) :: (k', v') :: rest
  | e :: rest -> e :: dict_insert k v rest

(* What [key] holds in a map; one that may be missing gives an Option. *)
let field key fields =
  match (List.assoc_opt key fields, Util.may_miss key) with
  | Some v, false -> v
  | Some v, true -> Ctor ("Some", [ v ])
  | None, true -> Ctor ("None", [])
  | None, false -> raise (Internal ("missing key :" ^ key))

(* A step of a path at run time: a map's key, or an index or dictionary key. *)
type step = Key of string | At of t

(* [v] with what is at [path] replaced by [f (Some old)], or [f None] when
   [adds] (set) and the last step is missing. A missing index, dictionary key
   or key that may be missing leaves [v] unaltered; another missing map
   key cannot happen, the types rule it out. *)
let rec change ~adds v path f =
  let last = path <> [] && List.tl path = [] in
  match (path, v) with
  | [], _ -> f (Some v)
  | Key k :: rest, Record fields -> (
      match List.assoc_opt k fields with
      | Some old ->
          Record
            (List.map
               (fun (k', x) -> if k' = k then (k', change ~adds old rest f) else (k', x))
               fields)
      | None when adds && last -> Record (fields @ [ (k, f None) ])
      | None when Util.may_miss k -> v
      | None -> raise (Internal ("missing key :" ^ k)))
  | At (Int i) :: rest, (Vector items | Buffer items) ->
      let n = Array.length items in
      let like items = match v with Buffer _ -> Buffer items | _ -> Vector items in
      if Z.fits_int i && Z.to_int i >= 0 && Z.to_int i < n then (
        (* No one else sees a buffer: it changes in place, once its new
           element is made, so what makes it reads the old one. *)
        let into = match v with Buffer _ -> items | _ -> Array.copy items in
        into.(Z.to_int i) <- change ~adds items.(Z.to_int i) rest f;
        like into)
      else if adds && last && Z.equal i (Z.of_int n) then
        like (Array.append items [| f None |])
      else v
  | At key :: rest, Dict entries -> (
      match List.find_opt (fun (k, _) -> compare k key = 0) entries with
      | Some (_, old) -> Dict (dict_insert key (change ~adds old rest f) entries)
      | None when adds && last -> Dict (dict_insert key (f None) entries)
      | None -> v)
  | _ -> raise (Internal "a path through a value of the wrong kind")

(* What is at [path] in [v], as an Option when a step can be missing (an
   index, a dictionary key, or a key that may be missing); another missing
   map key cannot happen. *)
let get v path =
  let rec find v path =
    match (path, v) with
    | [], _ -> Some v
    | Key k :: rest, Record fields -> (
        match List.assoc_opt k fields with
        | Some x -> find x rest
        | None when Util.may_miss k -> None
        | None -> raise (Internal ("missing key :" ^ k)))
    | At (Int i) :: rest, (Vector items | Buffer items) ->
        if Z.fits_int i && Z.to_int i >= 0 && Z.to_int i < Array.length items then
          find items.(Z.to_int i) rest
        else None
    | At key :: rest, Dict entries -> (
        match List.find_opt (fun (k, _) -> compare k key = 0) entries with
        | Some (_, x) -> find x rest
        | None -> None)
    | _ -> raise (Internal "a path through a value of the wrong kind")
  in
  let found = find v path in
  if List.exists (function At _ -> true | Key k -> Util.may_miss k) path then
    match found with Some x -> Ctor ("Some", [ x ]) | None -> Ctor ("None", [])
  else
    match found with Some x -> x | None -> raise (Internal "a key path found nothing")
