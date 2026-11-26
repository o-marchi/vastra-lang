(* The clock and timers, natively: what clock/elapsed reads and what
   clock/sleep waits on, which the interpreter, built programs and a window's
   frames run. A page's runtime sets [elapsed] and [after] to the browser's. *)

(* Seconds since the program started, from a clock that never jumps. *)
let elapsed = ref (fun () -> Mtime.Span.to_float_ns (Mtime_clock.elapsed ()) /. 1e9)

(* The timers waiting, in the order they are due; two due at the same moment,
   in the order they were set. *)
module Timers = Set.Make (struct
  type t = float * int * (unit -> unit)

  let compare (a, i, _) (b, j, _) = compare (a, i) (b, j)
end)

let timers = ref Timers.empty
let made = ref 0

(* Runs [f] after [seconds], and gives what calls it off. *)
let after =
  ref (fun seconds f ->
      incr made;
      let timer = (!elapsed () +. seconds, !made, f) in
      timers := Timers.add timer !timers;
      fun () -> timers := Timers.remove timer !timers)

let pending () = not (Timers.is_empty !timers)

(* The seconds until the next timer is due, if one is waiting. *)
let next () = Option.map (fun (at, _, _) -> at -. !elapsed ()) (Timers.min_elt_opt !timers)

let clear () = timers := Timers.empty

let fire ((_, _, f) as timer) =
  timers := Timers.remove timer !timers;
  f ()

(* Runs the timers that are due, one at a time. *)
let rec run_due () =
  match Timers.min_elt_opt !timers with
  | Some ((at, _, _) as timer) when at <= !elapsed () ->
      fire timer;
      run_due ()
  | _ -> ()

(* Runs the timers as they come due, until [until] holds or none is left. It
   sleeps a twentieth of a second at most at a time, so Ctrl+C is noticed. *)
let rec run ?(until = fun () -> false) () =
  match Timers.min_elt_opt !timers with
  | Some ((at, _, _) as timer) when not (until ()) ->
      let wait = at -. !elapsed () in
      if wait > 0. then Unix.sleepf (Float.min wait 0.05) else fire timer;
      run ~until ()
  | _ -> ()
