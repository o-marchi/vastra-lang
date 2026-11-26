(* The REPL: in a terminal, its own terminal; piped input, a line at a time.
   Either way a form is submitted once complete: Enter inside an open ( or
   string goes on. [respond] answers the requests (Session.respond): for a
   session here, or in a web page (vastra serve). *)

open Vastra
open Terminal

let prompt = "vastra> "
let continuation = "  ...> "

let help =
  {|Enter an expression or a definition. Its value and type are printed.

  (let name value)               define a value
  (fn name [params] body)        define a function
  (name args ...)                call it

Core forms:  let fn set update if cond match do type macro ns
             {:key value} (:key map) [vectors] -> ->> for later str
Types:       Int Float String Bool Unit [a] (Dict k v)
             (Option a) (Result e a)

Editing:     Enter evaluates a complete form, or starts a new line;
             Ctrl+J always starts one. Up and Down on the first and last
             line go through the history: with text typed, the entries
             starting with it, then those containing it. Tab completes
             a name; ? on an empty input shows the keys. The status line
             checks the input as you type, without running it.
             Ctrl+C stops an evaluation, or clears the input (so does
             Esc Esc); Ctrl+L clears the screen
Commands:    (typing : lists them)
             :type EXPR     the type of an expression, without running it
             :doc NAME      a definition's type and documentation
             :why           the last error's rule, its reason and examples
             :dir [PREFIX]  this session's definitions, or every name
                            starting with PREFIX, with their types
             *1 *2 *3       the last three values printed
             :save FILE     write this session's definitions to FILE
             :watch EXPR    an expression's value, kept above the prompt
             :open [EXPR]   look through a value, or the session's
                            definitions; Ctrl+O opens the last result
             :help  :quit  (or Ctrl+D)

Redefining a name updates every function that uses it. If the new
definition changes the name's type, whatever depends on it must still fit,
or be redefined in the same submission.|}

(* A command is :word followed by an argument; a lone keyword is an expression. *)
let command_of source =
  let line = String.trim source in
  match String.index_opt line ' ' with
  | Some i when line.[0] = ':' ->
      Some (String.sub line 0 i, String.trim (String.sub line i (String.length line - i)))
  | _ when List.mem line [ ":quit"; ":q"; ":help"; ":h"; ":dir"; ":open"; ":why" ] ->
      Some (line, "")
  | _ -> None

let command respond name arg =
  match name with
  | ":type" -> respond "type" arg
  | ":doc" -> respond "doc" arg
  | ":dir" -> respond "dir" arg
  | ":why" -> respond "why" arg
  | ":help" | ":h" -> [ Session.Note help ]
  | ":watch" | ":open" -> [ Session.refused (name ^ " works in a terminal") ]
  | ":save" -> (
      match respond "save" "" with
      | [ Session.Note code ] -> (
          match Out_channel.with_open_text arg (fun oc -> output_string oc code) with
          | () -> [ Session.Note ("saved this session's definitions to " ^ arg) ]
          | exception Sys_error m -> [ Session.refused ("cannot save: " ^ m) ])
      | parts -> parts)
  | _ -> [ Session.refused (Printf.sprintf "unknown command %s (try :help)" name) ]

(* What [source] gives, or None to quit. *)
let handle respond source =
  match command_of source with
  | Some ((":quit" | ":q"), _) -> None
  | Some (name, arg) -> Some (command respond name arg)
  | None when String.trim source = "" -> Some []
  | None -> Some (respond "eval" source)

(* $XDG_STATE_HOME/vastra/history (default ~/.local/state/vastra/history). *)
let history_file () =
  let base =
    match Sys.getenv_opt "XDG_STATE_HOME" with
    | Some d when d <> "" -> Some d
    | _ -> Option.map (fun h -> Filename.concat h ".local/state") (Sys.getenv_opt "HOME")
  in
  Option.bind base (fun base ->
      let dir = Filename.concat base "vastra" in
      let rec mkdir d =
        if not (Sys.file_exists d) then (
          mkdir (Filename.dirname d);
          Sys.mkdir d 0o755)
      in
      match mkdir dir with
      | () -> Some (Filename.concat dir "history")
      | exception Sys_error _ -> None)

(* The terminal *)

(* What comes to the terminal's loop from other threads: text to print above
   the live area (vastra serve's messages, what tasks print), and requests'
   answers, in the order they came. The pipe wakes the loop. *)
type printed = Message of string | Output of string | Error_output of string | Answer of (unit -> unit)

let queue = Queue.create ()
let lock = Mutex.create ()
let wake = ref None

let push printed =
  match !wake with
  | Some (_, w) ->
      Mutex.protect lock (fun () -> Queue.push printed queue);
      ignore (Unix.write_substring w "." 0 1)
  | None -> (
      match printed with
      | Message t | Output t -> print_endline t
      | Error_output t -> prerr_endline t
      | Answer f -> f ())

let announce text =
  let n = String.length text in
  push (Message (if n > 0 && text.[n - 1] = '\n' then String.sub text 0 (n - 1) else text))

(* Under vastra serve, what the pages are doing: the creature's pose and the
   words beside it, on the status line instead of in the transcript, and a
   passing pose (a cheer, a spin) until a time. Without a terminal, serve's
   [message] prints instead, as before. *)
let page = ref None
let passing = ref (Creature.Resting, 0.)

let tell_page ?pass ?message pose words =
  page := Some (pose, words);
  Option.iter (fun (p, seconds) -> passing := (p, Unix.gettimeofday () +. seconds)) pass;
  match !wake with
  | Some (_, w) -> ignore (Unix.write_substring w "." 0 1)
  | None -> Option.iter announce message

(* A saved file's error under vastra serve, in the live area until a save
   fixes it. With no live area, an error prints as its file breaks. *)
let broken = ref None

let show_broken ?error first =
  broken := first;
  match !wake with
  | Some (_, w) -> ignore (Unix.write_substring w "." 0 1)
  | None -> Option.iter print_endline error

(* Requests run one at a time on a thread of their own, so typing goes on
   while an evaluation runs or a page answers. [later f k] runs [f] there, then
   gives [k] its result in the terminal's loop. Between requests that thread
   runs the timers that come due, so tasks go on while the prompt waits;
   the pipe wakes it for a request. *)
let jobs = Queue.create ()
let jobs_lock = Mutex.create ()
let job_ready, job_added = Unix.pipe ~cloexec:true ()

let later f k =
  Mutex.protect jobs_lock (fun () ->
      Queue.push
        (fun () ->
          let x = f () in
          push (Answer (fun () -> k x)))
        jobs);
  ignore (Unix.write_substring job_added "." 0 1)

(* What the timers' tasks print shows above the prompt, and so does an error
   none of them can take. A Ctrl+C was for a request. *)
let run_timers () =
  Atomic.set Eval.stop false;
  try Clock.run_due () with
  | Diagnostic.Error d -> push (Error_output (Session.render_running d))
  | e ->
      let d = Diagnostic.bug Diagnostic.nowhere (Printexc.to_string e) in
      push (Error_output (Diagnostic.render d "" ""))

let rec work () =
  (match Mutex.protect jobs_lock (fun () -> Queue.take_opt jobs) with
  | Some job -> job ()
  | None -> (
      match Clock.next () with
      | Some wait when wait <= 0. -> run_timers ()
      | next -> (
          match Unix.select [ job_ready ] [] [] (Option.value next ~default:(-1.)) with
          | [ _ ], _, _ -> ignore (Unix.read job_ready (Bytes.create 64) 0 64)
          | _ | (exception Unix.Unix_error (EINTR, _, _)) -> ())));
  work ()

(* The submission running: its number, when it started, and when Ctrl+C asked
   it to stop. *)
type busy = { id : int; started : float; mutable stopping : float option }

let busy = ref None
let submissions = ref 0
let checking = ref false (* a check has been asked for *)
(* Watched expressions, each with its last answer and whether that changed it. *)
type watched = {
  expr : string;
  mutable parts : Session.part list;
  mutable changed : bool;
}

let watching = ref []
let watched_at = ref 0.
let recent = Hashtbl.create 8 (* a watched number's last values, newest first *)

(* Each result read back, by its source, to mark what changes when it is
   evaluated again; and the last result, while ↓ would show more of it. *)
let previous = Hashtbl.create 16
let unfold = ref None
let opened = ref None (* the last result's source and value, for Ctrl+O *)

(* The newest result while it may change: kept in the live area and
   asked for again each second, then printed as it last was when the next
   submission comes. Only a quick one with no call that acts (!) and no task
   run (@), so that asking again does nothing else. *)
type held = { source : string; mutable rows : Look.cell list list; mutable asked : float }

let held = ref None
let settles source = not (String.contains source '!' || String.contains source '@')

let freeze () =
  Option.iter (fun h -> Screen.print (h.rows @ [ [] ])) !held;
  held := None
let exploring = ref false
let input = Input.create ()
let history = Input.history []

(* A menu of names (completing from [start], out of [all]), or of commands. *)
type kind = Names of { start : int; all : (string * Look.cell list) list } | Commands
type menu = { items : (string * Look.cell list) list; mutable sel : int; kind : kind }

let menu = ref None
let keys_shown = ref false
let note = ref "" (* a word in the status line, until the next key *)
let failed = ref false (* the last submission's answer was an error *)

(* Under vastra serve, a submission whose tab closed before answering, while
   another is open: Enter on an empty input runs it there. *)
let again = Atomic.make false
let offer_again () = Atomic.set again true
let retry = ref None
let checked = ref ("", []) (* the input last checked, and what it gave *)
let edited_at = ref 0.
let quiet_for t = Unix.gettimeofday () -. !edited_at >= t
let problem_of = List.find_map (function Session.Problem p -> Some p | _ -> None)
let wavy (st : Look.style) = { st with wavy = Some (Theme.error ()) }

(* Errors wait for a longer pause than types. *)
let shown_problem () =
  match problem_of (snd !checked) with
  | Some p when fst !checked = input.text && quiet_for 0.5 -> Some p
  | _ -> None

(* The fix a shown error gives on its try: line, which Tab writes into the
   input: the line itself, and those after it, indented under it. *)
let try_of (p : Session.problem) =
  match List.find_index (String.starts_with ~prefix:"try: ") p.notes with
  | None -> None
  | Some i ->
      let line l = String.sub l 5 (String.length l - 5) in
      Some (String.concat "\n" (List.map line (List.filteri (fun j _ -> j >= i) p.notes)))
let last_esc = ref 0.
let ink () = Look.fg (Theme.ink ())
let muted () = Look.fg (Theme.muted ())
let lines style text = List.map (Look.text style) (String.split_on_char '\n' text)
let cross () = Look.text (Look.fg (Theme.error ())) " ✗ "

(* The matching bracket at the cursor, and what history browsing matched. *)
let marks () =
  let t = input.text and p = input.pos in
  let cls = Syntax.classify t in
  let bracket i = i >= 0 && i < String.length t && cls.(i) = Syntax.Bracket in
  let i = if bracket (p - 1) then p - 1 else p in
  let lit (st : Look.style) = { st with fg = Some (Theme.ink ()); bold = true } in
  let deep (st : Look.style) = { st with bg = Some (Theme.selected ()) } in
  (match if bracket i then Syntax.matching t cls i else None with
  | Some j -> [ (i, i + 1, lit); (j, j + 1, lit) ]
  | None -> [])
  @ (match shown_problem () with Some p when p.start < p.stop -> [ (p.start, p.stop, wavy) ] | _ -> [])
  @
  match Term.find t history.typed with
  | Some k when history.at >= 0 && history.typed <> "" -> [ (k, k + String.length history.typed, deep) ]
  | _ -> []

(* The input's rows, each at most [w] wide, the cursor drawn as a cell. *)
let input_rows w =
  let t = input.text and p = input.pos in
  let faint = Look.fg (Theme.faint ()) in
  if t = "" then [ { Look.ch = "T"; style = Theme.cursor faint } :: Look.text faint "ry (map inc [1 2 3])" ]
  else
    let li = List.length (String.split_on_char '\n' (String.sub t 0 p)) - 1 in
    let col = Input.chars t (Input.line_start t p) p in
    let cursor (c : Look.cell) = { c with style = Theme.cursor c.style } in
    let with_cursor i row =
      if i <> li then row
      else if col < List.length row then List.mapi (fun k c -> if k = col then cursor c else c) row
      else row @ [ cursor { ch = " "; style = Look.plain } ]
    in
    List.concat (List.mapi (fun i row -> Look.chunks w (with_cursor i row)) (Look.lines (Theme.code ~marks:(marks ()) t)))

let hint () =
  let h = history in
  if h.at >= 0 then
    Look.text (muted ()) (Printf.sprintf "↑↓ %d of %d" (h.at + 1) (List.length h.found))
    @
    if h.typed = "" then []
    else Look.text (muted ()) " starting with " @ Theme.code (List.hd (String.split_on_char '\n' h.typed))
  else
    Look.text (muted ())
      (if !note <> "" then !note
       else if String.trim input.text = "" && !unfold <> None then "↓ prints the rest"
       else if String.trim input.text = "" && !retry <> None then
         "↵ runs it in the other tab · esc drops it"
       else if String.trim input.text = "" && !failed then "↑ brings it back · :why explains the rule"
       else if String.trim input.text = "" then "? for shortcuts"
       else if command_of input.text <> None then "↵ run"
       else if Reader.is_incomplete input.text then "↵ new line"
       else if Option.bind (shown_problem ()) try_of <> None then
         "tab takes the try: · ↵ evaluate"
       else "↵ evaluate")

let outcome_hint = function
  | Session.Outcome (Defined { name; ty }) ->
      Some
        (Look.text (muted ()) "defines " @ Look.text (Theme.bold (Theme.ink ())) name
        @ Look.text (muted ()) " : " @ Theme.types ty)
  | Outcome (Evaluated { ty; _ }) -> Some (Look.text (muted ()) ": " @ Theme.types ty)
  | Outcome (Declared text) -> Some (Look.text (muted ()) text)
  | _ -> None

(* The live check, on the status line's left: while typing, what the last
   check said, unless it found an error. *)
let check_status () =
  let t = input.text in
  if String.trim t = "" || command_of t <> None then []
  else
    match (Reader.read_all t, shown_problem ()) with
    | Error { kind = Unclosed c; _ }, _ when quiet_for 0.12 -> Look.text (muted ()) (Printf.sprintf "%c still open" c)
    | Error { kind = Unterminated_string; _ }, _ when quiet_for 0.12 -> Look.text (muted ()) "a string still open"
    | _, Some p ->
        Look.text (Theme.bold (Theme.error ())) (if p.label = "" then "" else p.label ^ ": ")
        @ Look.text (ink ()) p.message
    | _ when problem_of (snd !checked) <> None -> []
    | _ ->
        List.concat
          (List.mapi
             (fun i h -> if i = 0 then h else Look.text (muted ()) " · " @ h)
             (List.filter_map outcome_hint (snd !checked)))

(* A row each, above the input: the value in gold when it just changed, a
   number's trail, or dimmed, why it can't be asked now. *)
let watch_rows () =
  let gold = Look.fg (Theme.thread ()) and faint = Look.fg (Theme.faint ()) in
  List.map
    (fun w ->
      let values = Option.value (Hashtbl.find_opt recent w.expr) ~default:[] in
      let value v =
        if w.changed then Look.text (Theme.bold (Theme.thread ())) v else Theme.code v
      in
      let trail =
        if List.length values < 3 then "" else " " ^ Show.bars (List.rev values)
      in
      Look.text gold " ◆ "
      @
      match (w.parts, problem_of w.parts) with
      | [ Session.Outcome (Evaluated { value = v; _ }) ], _ ->
          Theme.code w.expr @ Area.spaces 2 @ value v @ Look.text gold trail
      | _, Some p -> Look.text faint (w.expr ^ "  ✗ " ^ p.message)
      | _, None -> Look.text faint w.expr)
    !watching

let needs_check t = String.trim t <> "" && command_of t = None && not (Reader.is_incomplete t)

let commands =
  [
    (":type", "EXPR · the type of an expression, without running it");
    (":doc", "NAME · a definition's type and documentation");
    (":why", "the last error's rule, its reason and examples");
    (":dir", "[PREFIX] · the definitions, or the names starting with PREFIX");
    (":save", "FILE · write this session's definitions to FILE");
    (":watch", "EXPR · an expression's value, kept above the prompt, or no longer");
    (":open", "[EXPR] · look through a value, or the session's definitions");
    (":help", "keys, forms and commands");
    (":quit", "leave");
  ]

let takes_argument name = List.mem name [ ":type"; ":doc"; ":save"; ":watch" ]

let key_rows () =
  let key k = Look.text (Look.fg (Theme.thread ())) k @ Area.spaces (9 - Input.chars k 0 (String.length k)) in
  let row k d k2 d2 =
    Area.indent @ key k @ Look.text (muted ()) d @ Area.spaces (30 - String.length d) @ key k2 @ Look.text (muted ()) d2
  in
  [
    row "↵" "evaluate, or a new line" "tab" "complete a name";
    row "ctrl+j" "a new line, always" ":" "commands";
    row "↑ ↓" "history matching the input" "esc esc" "clear the input";
    row "ctrl+c" "stop, or clear the input" "ctrl+d" "quit";
    row "ctrl+l" "clear the screen" "?" "these keys";
    row "ctrl+o" "open the last result" "↓" "the rest of a result";
  ]

(* Above the input, as an error in the transcript reads. *)
let broken_rows () =
  match Option.map (String.split_on_char '\n') !broken with
  | Some (first :: rest) ->
      let i = Option.fold ~none:0 ~some:(( + ) 2) (Term.find first ": ") in
      (cross () @ Look.text (Theme.bold (Theme.error ())) (String.sub first 0 i)
      @ Look.text (ink ()) (String.sub first i (String.length first - i)))
      :: List.map (fun l -> Area.indent @ Look.text (muted ()) l) rest
      @ [ [] ]
  | _ -> []

(* Under vastra serve with no page open, an evaluation is held for the first. *)
let waits_for_page () =
  match !page with Some ((Creature.Waving | Asleep), _) -> true | _ -> false

(* The creature's pose now: weaving while an evaluation runs, unless it
   waits for a page; else a passing pose; else what serve last said. *)
let pose now =
  let settled = match !page with Some (p, _) -> p | None -> Creature.Resting in
  match (!busy, !passing) with
  | Some _, _ -> if waits_for_page () then Creature.Waving else Weaving
  | None, (p, until) when now < until -> p
  | None, _ -> settled

(* The row fixed at the top: the creature and the name, and on the right what
   serve's pages are doing. *)
let top_row now =
  let left =
    Look.text Look.plain " " @ Creature.cells (pose now) now
    @ Look.text (Theme.bold (Theme.ink ())) " vastra"
    @ Look.text (muted ()) " 0.1.0 · pre-alpha"
  in
  let right =
    match !page with Some (_, w) when w <> "" -> Look.text (muted ()) w | _ -> []
  in
  left @ Area.spaces (!Screen.width - 2 - Look.width left - Look.width right) @ right

(* An error's notes go under the status line, which holds only its message. *)
let draw () =
  let now = Unix.gettimeofday () in
  let held_rows =
    match !held with
    | Some { rows = first :: rest; _ } when not !exploring ->
        let mark = Look.text (Look.fg (Theme.thread ())) " ◦ " in
        (mark @ List.filteri (fun i _ -> i >= Area.edge) first) :: rest
    | _ -> []
  in
  let top =
    held_rows @ broken_rows () @ watch_rows ()
    @
    match !busy with
    | Some _ when waits_for_page () ->
        let faint = Look.fg (Theme.faint ()) in
        [ Area.indent @ Look.text faint "⋯ held until a page connects"; [] ]
    | Some b when now -. b.started > 0.15 -> [ Waiting.row ~elapsed:(now -. b.started); [] ]
    | _ when !exploring -> Explore.rows ~width:!Screen.width ~height:!Screen.height
    | _ -> []
  in
  let below, status, notes =
    match (!menu, !keys_shown) with
    | Some m, _ ->
        (Area.menu_rows m.items m.sel, Some ([], Look.text (muted ()) "↑↓ choose · tab accept · esc close"), [])
    | None, true -> (key_rows (), None, [])
    | None, false ->
        let notes = match shown_problem () with Some p -> p.notes | None -> [] in
        ( [],
          Some
            ( check_status (),
              if !exploring then Explore.hint () else hint () ),
          List.map (fun n -> Area.indent @ Look.text (muted ()) n) notes )
  in
  Screen.pin (top_row now);
  Screen.draw (Area.rows ~width:!Screen.width ~top ~input:input_rows ~below ~status ~busy:(!busy <> None) @ notes)

let name_start s i =
  let rec go j = if j > 0 && not (String.contains " \n\t()[]{}\"@'`~^," s.[j - 1]) then go (j - 1) else j in
  go i

let starting prefix = List.filter (fun (name, _) -> String.starts_with ~prefix name)

(* After an edit: typing : lists the commands; a list of names narrows. *)
let refresh_menu () =
  let t = input.text in
  menu :=
    if t <> "" && t.[0] = ':' && not (String.contains t ' ' || String.contains t '\n') then
      match starting t (List.map (fun (n, d) -> (n, Look.text (muted ()) d)) commands) with
      | [] -> None
      | items -> Some { items; sel = 0; kind = Commands }
    else
      match !menu with
      | Some { kind = Names { start; all }; sel; _ } when start <= input.pos && name_start t input.pos = start -> (
          match starting (String.sub t start (input.pos - start)) all with
          | [] -> None
          | items -> Some { items; sel = min sel (List.length items - 1); kind = Names { start; all } })
      | _ -> None

(* Tab: the names starting with what is before the cursor, with their types. *)
let complete respond =
  let start = name_start input.text input.pos in
  let prefix = String.sub input.text start (input.pos - start) in
  let named = function
    | Session.Note l -> (
        match Term.find l " : " with
        | Some i -> Some (String.sub l 0 i, Theme.types (String.sub l (i + 3) (String.length l - i - 3)))
        | None -> None)
    | _ -> None
  in
  let text = input.text and pos = input.pos in
  (* Shown only if nothing was typed meanwhile. *)
  if prefix <> "" then
    later
      (fun () -> List.filter_map named (respond "dir" prefix))
      (fun names ->
        if input.text = text && input.pos = pos then
          match names with
          | [] -> note := "no name starts with " ^ prefix
          | [ (name, _) ] -> Input.replace input start input.pos name
          | all -> menu := Some { items = all; sel = 0; kind = Names { start; all } })

let take_queue () =
  Mutex.protect lock (fun () ->
      let printed = List.of_seq (Queue.to_seq queue) in
      Queue.clear queue;
      printed)

(* What tasks print lines up with results; messages from elsewhere stand apart. *)
let printed_rows = function
  | Output t -> List.map (fun r -> Area.indent @ r) (lines (ink ()) t)
  | Error_output t -> List.map (fun r -> Area.indent @ r) (lines (Look.fg (Theme.error ())) t)
  | Answer _ -> []
  | Message t ->
      List.mapi
        (fun i r -> Look.text (Look.fg (Theme.faint ())) (if i = 0 then " · " else "   ") @ r)
        (lines (muted ()) t)
      @ [ [] ]

let print_queue () =
  List.iter (function Answer f -> f () | printed -> Screen.print (printed_rows printed)) (take_queue ())

let echo ?(marks = []) source =
  let rec stop i = if i > 0 && String.contains " \t\n" source.[i - 1] then stop (i - 1) else i in
  let source = String.sub source 0 (stop (String.length source)) in
  let width = !Screen.width - 1 - Area.edge in
  List.map Area.on_strip (Area.prompted (List.concat_map (Look.chunks width) (Look.lines (Theme.code ~marks source))))

(* A part of the answer to [source], as rows. An error is shown as a file's
   is, quoting the submission with its marks; with nowhere to show, its
   message and notes are enough. *)
let part_rows ?(nth = 0) source =
  (* After the value if both fit on its line, or on lines of its own. *)
  let typed shown ty =
    let rows =
      match (Look.lines shown, Look.lines (Theme.types ty)) with
      | [ one ], [ t ] when Look.width one + 3 + Look.width t <= !Screen.width - Area.edge
        ->
          [ one @ Look.text (muted ()) " : " @ t ]
      | shown, t :: ts -> shown @ ((Look.text (muted ()) ": " @ t) :: ts)
      | shown, [] -> shown
    in
    List.map (fun r -> Area.indent @ r) rows
  in
  function
  | Session.Outcome (Defined { name; ty }) ->
      typed (Look.text (Theme.bold (Theme.ink ())) name) ty
  | Outcome (Evaluated { value; ty }) -> (
      (* Laid out by its shape, or else as code is laid out. *)
      let key = string_of_int nth ^ " " ^ source in
      match Show.result ?prev:(Hashtbl.find_opt previous key) ~width:(!Screen.width - Area.edge) value ty with
      | Some (rows, read, more) ->
          Hashtbl.replace previous key read;
          unfold := if more then Some (value, ty) else None;
          opened := Some (String.trim source, value);
          List.map (fun r -> Area.indent @ r) rows
      | None -> typed (Theme.code value) ty)
  | Outcome (Declared text) -> [ Area.indent @ Look.text (muted ()) text ]
  | Outcome (Failed (e, _)) -> [ cross () @ Look.text (ink ()) ("task failed: " ^ e) ]
  | Problem { label = ""; message; _ } -> [ cross () @ Look.text (ink ()) message ]
  | Problem p ->
      (cross () @ Look.text (Theme.bold (Theme.error ())) (p.label ^ ": ") @ Look.text (ink ()) p.message)
      :: List.map
           (fun l -> Area.indent @ Look.text (muted ()) l)
           (if p.start >= p.stop then p.notes else List.tl (String.split_on_char '\n' p.text))
  | Note text -> (
      match (command_of source, Term.find text " : ") with
      | Some (":type", arg), _ -> typed (Theme.code arg) text
      | Some (":dir", _), Some i ->
          let ty = String.sub text (i + 3) (String.length text - i - 3) in
          typed (Look.text (ink ()) (String.sub text 0 i)) ty
      | _ -> List.map (fun r -> Area.indent @ r) (lines (ink ()) text))
  | Output text -> printed_rows (Output text)

(* Under the top row, which names vastra. *)
let banner about =
  List.map (fun l -> Area.spaces 7 @ Look.text (muted ()) l) (String.split_on_char '\n' about)
  @ [ [] ]

(* A watched number's last values, for its trail. *)
let remember expr x =
  let before = Option.value (Hashtbl.find_opt recent expr) ~default:[] in
  Hashtbl.replace recent expr (List.filteri (fun i _ -> i < 12) (x :: before))

(* Each watched expression asked for again, without touching *1. One that
   can't be asked now (a save broke it) stays, showing why. *)
let refresh_watch respond =
  List.iter
    (fun w ->
      later
        (fun () -> respond "peek" w.expr)
        (fun parts ->
          (match parts with
          | [ Session.Outcome (Evaluated { value; _ }) ] -> (
              match float_of_string_opt value with
              | Some x -> remember w.expr x
              | None -> ())
          | _ -> ());
          w.changed <- w.parts <> [] && w.parts <> parts;
          w.parts <- parts))
    !watching

(* :watch EXPR again stops it. Asking again must do nothing else, so an
   expression that acts (!) or runs a task (@) is refused. *)
let watch respond expr =
  let expr = String.trim expr in
  let was = List.exists (fun w -> w.expr = expr) !watching in
  if not (was || settles expr) then
    let why =
      "only an expression with no ! and no @ can be watched:"
      ^ " asking again must do nothing else"
    in
    Screen.print [ cross () @ Look.text (ink ()) why; [] ]
  else (
    watching :=
      if was then List.filter (fun w -> w.expr <> expr) !watching
      else !watching @ [ { expr; parts = []; changed = false } ];
    if not was then refresh_watch respond;
    let said = (if was then "no longer watching " else "watching ") ^ expr in
    Screen.print [ Area.indent @ Look.text (muted ()) said; [] ])

(* The answer to submission [id], unless Ctrl+C stopped waiting for it. *)
let finish respond id source parts =
  match !busy with
  | Some b when b.id = id ->
      busy := None;
      let elapsed = Unix.gettimeofday () -. b.started in
      unfold := None;
      failed := problem_of parts <> None;
      retry := if Atomic.exchange again false then Some source else None;
      let rows = List.concat (List.mapi (fun nth part -> part_rows ~nth source part) parts) in
      (* A slow success ends with how long it took. *)
      let last = List.length rows - 1 in
      let took i r =
        if i = last && elapsed >= 1. && problem_of parts = None then
          r @ Look.text (muted ()) (Printf.sprintf " · %.1fs" elapsed)
        else r
      in
      (match parts with
      | [ Outcome (Evaluated _) ] when elapsed < 0.2 && settles source && List.length rows <= 8 ->
          held := Some { source; rows; asked = Unix.gettimeofday () }
      | _ -> Screen.print (List.mapi took rows @ [ [] ]));
      refresh_watch respond
  | _ -> ()

(* A held result asked for again; what changed shows in gold. *)
let refresh_held respond now =
  match !held with
  | Some h when !busy = None && now -. h.asked > 1. ->
      h.asked <- now;
      later
        (fun () -> respond "peek" h.source)
        (fun parts ->
          match (!held, parts) with
          | Some h', [ (Session.Outcome (Evaluated _) as o) ] when h' == h ->
              h.rows <- part_rows h.source o
          | _ -> ())
  | _ -> ()

(* Opening a value. The session's definitions come first, so that a name,
   or a path from one, opens at its place under that name. *)
let with_names respond k =
  later
    (fun () -> respond "dir" "")
    (fun parts ->
      let named = function
        | Session.Note l ->
            Option.map (fun i -> (String.sub l 0 i, String.sub l (i + 3) (String.length l - i - 3))) (Term.find l " : ")
        | _ -> None
      in
      Explore.at.names <- List.filter_map named parts;
      k ())

(* A value, evaluated without becoming *1. *)
let peek respond code k =
  later
    (fun () -> respond "peek" code)
    (fun parts ->
      match List.find_map (function Session.Outcome (Evaluated { value; _ }) -> Some value | _ -> None) parts with
      | Some value -> (
          match Reader.read_all value with Ok [ n ] -> k n | _ -> note := "this value can't be opened")
      | None -> note := match problem_of parts with Some p -> p.message | None -> "nothing to open")

let shown () =
  Input.set input (Explore.code ());
  edited_at := Unix.gettimeofday ()

(* [source] opens at its place when it is a name or a path from one; otherwise
   as the value it gives, [value] when already printed. *)
let explore respond source value =
  let start base steps =
    Explore.opening ~steps (Some base);
    exploring := true;
    shown ()
  in
  let step (s : Reader.node) =
    match s.form with
    | Keyword _ -> Explore.Key s
    | Int i when Z.fits_int i -> Explore.At (Z.to_int i)
    | _ -> Explore.Entry s
  in
  with_names respond (fun () ->
      match (Reader.read_all source, value) with
      | Ok [], _ ->
          Explore.opening None;
          exploring := true;
          shown ()
      | Ok [ { form = Symbol name; _ } ], _ when List.mem_assoc name Explore.at.names ->
          peek respond name (fun n -> start (name, n) [])
      | Ok [ { form = List ({ form = Symbol "get"; _ } :: { form = Symbol name; _ } :: steps); _ } ], _
        when List.mem_assoc name Explore.at.names ->
          peek respond name (fun n -> start (name, n) (List.map step steps))
      | _, Some v -> ( match Reader.read_all v with Ok [ n ] -> start (source, n) [] | _ -> note := "this value can't be opened")
      | _, None -> peek respond source (fun n -> start (source, n) []))

(* The echo is plain: an error quotes the submission with its marks. *)
let submit respond =
  let source = input.text in
  Input.remember history source;
  Option.iter (fun path -> Input.save path history.entries) (history_file ());
  Input.set input "";
  failed := false;
  let print_echo () =
    freeze ();
    Screen.print (echo source)
  in
  match command_of source with
  | Some ((":quit" | ":q"), _) -> false
  | Some (":watch", name) ->
      print_echo ();
      watch respond name;
      true
  | Some (":open", code) ->
      print_echo ();
      explore respond code None;
      true
  | _ ->
      print_echo ();
      incr submissions;
      let id = !submissions in
      busy := Some { id; started = Unix.gettimeofday (); stopping = None };
      (* What it shows is laid out for the window. *)
      let width = string_of_int (!Screen.width - Area.edge) in
      let respond request arg = respond (request ^ " " ^ width) arg in
      later
        (fun () -> Option.value (handle respond source) ~default:[])
        (fun parts -> finish respond id source parts);
      true

let accept respond m ~enter =
  menu := None;
  let name = fst (List.nth m.items m.sel) in
  match m.kind with
  | Names { start; _ } ->
      Input.replace input start input.pos name;
      true
  | Commands when takes_argument name || ((name = ":dir" || name = ":open") && not enter) ->
      Input.set input (name ^ " ");
      true
  | Commands ->
      Input.set input name;
      (not enter) || submit respond

(* A key that edits the text, or submits it; [false] means quit. *)
let on_text respond key =
  match key with
  | Term.Enter when !busy <> None ->
      note := "an evaluation is running · ctrl+c stops it";
      true
  | Ctrl 'c' when !busy <> None ->
      Atomic.set Eval.stop true;
      Option.iter (fun b -> b.stopping <- Some (Unix.gettimeofday ())) !busy;
      true
  | Term.Enter when String.trim input.text = "" && !retry <> None ->
      Input.set input (Option.get !retry);
      retry := None;
      submit respond
  | Term.Enter ->
      if String.trim input.text = "" then true
      else if Reader.is_incomplete input.text then (
        Input.newline input;
        true)
      else submit respond
  | Ctrl 'd' when input.text = "" -> false
  | _ ->
      (match key with
      | Newline -> Input.newline input
      | Ctrl 'c' -> Input.set input ""
      | Esc ->
          if Unix.gettimeofday () -. !last_esc < 0.5 then Input.set input "";
          last_esc := Unix.gettimeofday ()
      | Ctrl 'l' -> Screen.clear ()
      | Up ->
          if not (Input.up input) then (
            match Input.older history input.text with
            | Some entry -> Input.set input entry
            | None -> note := if history.found = [] then "nothing earlier matches" else "the oldest match")
      | Down when input.text = "" && history.at < 0 && !unfold <> None ->
          (* The last result, whole. *)
          let value, ty = Option.get !unfold in
          unfold := None;
          Option.iter
            (fun (rows, _, _) -> Screen.print (List.map (fun r -> Area.indent @ r) rows @ [ [] ]))
            (Show.result ~budget:max_int ~deep:max_int ~width:(!Screen.width - Area.edge) value ty)
      | Down -> if not (Input.down input) then Option.iter (Input.set input) (Input.newer history)
      | Left -> Input.left input
      | Right -> Input.right input
      | Home | Ctrl 'a' -> Input.home input
      | End | Ctrl 'e' -> Input.end_ input
      | Backspace -> Input.backspace input
      | Delete | Ctrl 'd' -> Input.delete input
      | Ctrl 'u' -> Input.kill_before input
      | Ctrl 'k' -> Input.kill_after input
      | Ctrl 'w' -> Input.kill_word input
      | Char c -> Input.insert input c
      | Paste s -> Input.paste input s
      | _ -> ());
      true

(* [false] means quit. *)
let rec on_key respond key =
  match if !exploring then Explore.key key else Not_mine with
  | Moved ->
      shown ();
      true
  | Closed ->
      exploring := false;
      true
  | Open_name name ->
      peek respond name (fun n ->
          Explore.opening (Some (name, n));
          shown ());
      true
  | Up_to_session ->
      let from = Option.map fst Explore.at.base in
      with_names respond (fun () ->
          Explore.opening None;
          Explore.at.sel <- Option.value ~default:0 (List.find_index (fun (n, _) -> Some n = from) Explore.at.names);
          shown ());
      true
  | Not_mine ->
      exploring := false;
      edit_key respond key

and edit_key respond key =
  let before = input.text in
  if key <> Term.Enter then retry := None;
  note := "";
  let was_shown = !keys_shown in
  keys_shown := false;
  let go_on =
    match (key, !menu) with
    | (Term.Up | Down), Some m ->
        m.sel <- (if key = Up then max 0 (m.sel - 1) else min (List.length m.items - 1) (m.sel + 1));
        true
    | (Tab | Enter), Some m -> accept respond m ~enter:(key = Enter)
    | Esc, Some _ ->
        menu := None;
        true
    | Char "?", None when input.text = "" ->
        keys_shown := not was_shown;
        true
    | Tab, None ->
        (match Option.bind (shown_problem ()) try_of with
        | Some fix -> Input.set input fix
        | None -> complete respond);
        true
    | Ctrl 'o', None ->
        (match !opened with
        | Some (source, value) -> explore respond source (Some value)
        | None -> note := "nothing printed yet to open");
        true
    | _ -> on_text respond key
  in
  (* Typing ends the browsing: the next Up searches for the new text. *)
  if input.text <> before then edited_at := Unix.gettimeofday ();
  if input.text <> before && key <> Up && key <> Down then (
    history.at <- -1;
    refresh_menu ());
  go_on

(* None if the terminal does not answer where its cursor is: then the input is
   read a line at a time. *)
let interactive ~about respond =
  Look.mode := Look.mode_of_env ();
  Term.raw ();
  Term.ask_background ();
  if not (Screen.start ()) then (
    Term.restore ();
    None)
  else (
    Theme.choose (Term.background ());
    let r, w = Unix.pipe ~cloexec:true () in
    wake := Some (r, w);
    ignore (Thread.create work ());
    Term.watch_size ();
    Builtins.print := (fun t -> push (Output t));
    Builtins.print_error := (fun t -> push (Error_output t));
    history.entries <- Option.fold ~none:[] ~some:Input.load (history_file ());
    Screen.pin (top_row (Unix.gettimeofday ()));
    Screen.print (banner about);
    draw ();
    let rec loop () =
      if !Term.resized then (
        Term.resized := false;
        Screen.resize ();
        draw ());
      let now = Unix.gettimeofday () in
      (* Checked once typing pauses, and not while evaluating. *)
      let text = input.text in
      if fst !checked <> text && quiet_for 0.12 && !busy = None && not !checking then
        if needs_check text then (
          checking := true;
          later
            (fun () -> respond "check" text)
            (fun parts ->
              checking := false;
              checked := (text, parts)))
        else checked := (text, []);
      (* A page cannot be stopped from here: after Ctrl+C, stop waiting for it. *)
      (match !busy with
      | Some { stopping = Some t; _ } when now -. t > 0.5 ->
          busy := None;
          Screen.print [ cross () @ Look.text (ink ()) "stopped waiting for the page, which goes on evaluating"; [] ]
      | _ -> ());
      (* A page's names change without submissions. *)
      if !watching <> [] && !busy = None && now -. !watched_at > 1. then (
        watched_at := now;
        refresh_watch respond);
      refresh_held respond now;
      let animating = !busy <> None || Creature.moves (pose now) in
      let waiting = animating || fst !checked <> text || (problem_of (snd !checked) <> None && not (quiet_for 0.5)) in
      match Unix.select [ Unix.stdin; r ] [] [] (if waiting then 0.09 else 1.) with
      | exception Unix.Unix_error (EINTR, _, _) -> loop ()
      | [], _, _ ->
          draw ();
          loop ()
      | ready, _, _ ->
          if List.mem r ready then ignore (Unix.read r (Bytes.create 256) 0 256);
          print_queue ();
          if List.mem Unix.stdin ready then Term.read ();
          if keys () then (
            draw ();
            loop ())
    and keys () = match Term.key () with None -> true | Some k -> on_key respond k && keys () in
    Fun.protect
      ~finally:(fun () ->
        freeze ();
        Screen.stop ();
        Term.restore ();
        wake := None)
      loop;
    Some 0)

let piped respond =
  let buffer = Buffer.create 256 in
  let show =
    List.iter (function
      | Session.Problem _ as p -> prerr_endline (Session.text p)
      | p -> print_endline (Session.text p))
  in
  let rec loop () =
    print_string (if Buffer.length buffer = 0 then prompt else continuation);
    flush stdout;
    match In_channel.input_line stdin with
    | None ->
        print_newline ();
        if String.trim (Buffer.contents buffer) <> "" then show (respond "eval" (Buffer.contents buffer));
        0
    | Some line when not (String.is_valid_utf_8 line) ->
        prerr_endline "error reading input: stream did not contain valid UTF-8";
        1
    | Some line -> (
        let line =
          if String.ends_with ~suffix:"\r" line then String.sub line 0 (String.length line - 1)
          else line
        in
        Buffer.add_string buffer (line ^ "\n");
        if Reader.is_incomplete (Buffer.contents buffer) then loop ()
        else
          let source = Buffer.contents buffer in
          Buffer.clear buffer;
          match handle respond source with
          | None -> 0
          | Some parts ->
              show parts;
              loop ())
  in
  loop ()

let run ?(about = "Type :help for help, Ctrl+D to exit.") respond =
  let terminal =
    Unix.isatty Unix.stdin && Unix.isatty Unix.stdout && Sys.getenv_opt "TERM" <> Some "dumb"
  in
  match if terminal then interactive ~about respond else None with
  | Some code -> code
  | None ->
      print_endline ("Vastra 0.1.0 (pre-alpha). " ^ about);
      piped respond
