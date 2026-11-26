(* What shows while an evaluation is slow: the word and the seconds so
   far. The creature on the status line weaves meanwhile. *)

open Look

let row ~elapsed =
  Area.indent
  @ text (fg (Theme.muted ())) "evaluating"
  @ if elapsed >= 1. then text (fg (Theme.muted ())) (Printf.sprintf " · %ds" (int_of_float elapsed)) else []
