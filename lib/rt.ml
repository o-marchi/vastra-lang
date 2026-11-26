(* What compiled programs (see Compile) call at run time. *)

open Value

let internal message = raise (Internal message)

let apply f args =
  match f with
  | Builtin b -> b.run args
  | Keyword k -> (
      match args with
      | [ Record fields ] -> field k fields
      | _ -> internal "a keyword applied to something that is not a map")
  | _ -> internal "calling a value that is not a function"

let get key = function
  | Record fields -> field key fields
  | _ -> internal "reading a key from a value that is not a map"

let truth = function Bool b -> b | _ -> internal "if condition is not a Bool"
let fn name run = Builtin { builtin_name = name; run }
let constructor name = fn name (fun args -> Ctor (name, args))

(* A top-level expression: in a program its task runs, and the next line
   waits for it to end; otherwise its value is shown. *)
let show_mode = ref false
let names = ref [] (* qualified → as typed in the program's file *)
let failed = ref None

(* The program's file and its text, which its errors are shown in. *)
let source = ref ("", "")

let top value ty (start, stop) next =
  match value with
  | Task t when not !show_mode ->
      t (fun outcome ->
          (match outcome with
          | Error e when !failed = None ->
              failed := Some (Diagnostic.untaken { start; stop } (to_string e))
          | _ -> ());
          next ())
  | v ->
      let name n = Option.value (List.assoc_opt n !names) ~default:n in
      if !show_mode then print_endline (to_string ~name v ^ " : " ^ ty);
      next ()

(* Ends the process; a page keeps running, so its own acts only on failures. *)
let ends : (int -> unit) ref = ref (fun code -> exit code)

(* The program ends after its last line, and what it started stops with it:
   what is waiting never goes on. *)
let finish () =
  match !failed with
  | Some d ->
      prerr_endline (Diagnostic.render d (snd !source) (fst !source));
      !ends 1
  | None -> !ends !Builtins.exit_code

(* A definition's @ at the top level: its task runs, and the definition
   waits for its value, as the next line does; if it fails, the program stops. *)
let now value (start, stop) next =
  match value with
  | Task run -> (
      run (function
        | Ok v -> next v
        | Error e ->
            failed := Some (Diagnostic.untaken { start; stop } (to_string e));
            finish ()))
  | _ -> internal "running a definition's value that is not a task"

(* par/ on every core. The domains live across calls, since starting them
   costs too much in a frame loop. A caller waiting for its parts runs queued
   ones meanwhile, so a par/ inside a part never waits for a free domain. *)
let lock = Mutex.create ()
let changed = Condition.create ()
let jobs : (unit -> unit) Queue.t = Queue.create ()
let cores = Builtins.cores

let rec work () : unit =
  Mutex.lock lock;
  while Queue.is_empty jobs do
    Condition.wait changed lock
  done;
  let job = Queue.pop jobs in
  Mutex.unlock lock;
  job ();
  work ()

let domains = lazy (List.init (cores - 1) (fun _ -> Domain.spawn work))

(* One part per core, each a run of indices; the first part's exception wins,
   as the first element's would one at a time. *)
let parallel n f =
  let parts = min n cores in
  if parts <= 1 then Array.init n f
  else (
    Lazy.force domains |> ignore;
    let results = Array.make n Unit and failures = Array.make parts None in
    let left = ref parts in
    let part p () =
      (try
         for i = p * n / parts to ((p + 1) * n / parts) - 1 do
           results.(i) <- f i
         done
       with e -> failures.(p) <- Some e);
      Mutex.lock lock;
      decr left;
      Condition.broadcast changed;
      Mutex.unlock lock
    in
    Mutex.lock lock;
    for p = 1 to parts - 1 do
      Queue.push (part p) jobs
    done;
    Condition.broadcast changed;
    Mutex.unlock lock;
    part 0 ();
    Mutex.lock lock;
    while !left > 0 do
      if Queue.is_empty jobs then Condition.wait changed lock
      else
        let job = Queue.pop jobs in
        Mutex.unlock lock;
        job ();
        Mutex.lock lock
    done;
    Mutex.unlock lock;
    Array.iter (Option.iter raise) failures;
    results)

let main ?(exit = Stdlib.exit) body =
  Value.apply := apply;
  Builtins.parallel := parallel;
  Builtins.program_args := List.tl (Array.to_list Sys.argv);
  ends := exit;
  (Builtins.ending := fun () -> !ends !Builtins.exit_code);
  (* Natively the timers run until the last line ends the program; JavaScript
     runs its own. *)
  match
    body ();
    Clock.run ()
  with
  | () -> ()
  | exception Internal m ->
      prerr_endline (Diagnostic.render (Diagnostic.bug Diagnostic.nowhere m) "" "");
      exit 1
  | exception Stack_overflow ->
      prerr_endline
        "runtime error: evaluation is nested too deeply (native stack exhausted)";
      exit 1
