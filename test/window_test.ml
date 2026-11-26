(* vastra.window without a window: SDL's dummy video driver runs a program
   for three frames, key events are pushed between them, and the pixels of
   each frame are read back before it is shown. *)

open Tsdl
open Vastra

let failures = ref 0

let check name ok =
  if not ok then (
    incr failures;
    prerr_endline ("FAILED: " ^ name))

(* Each event the handlers get, as text; the picture is 3 by 2. *)
let program =
  {|(ns test (:require [vastra.window :as window] [vastra.console :as console]))
(let events [])
(let frames 0)
(let screen @(window/open {:title "test" :width 3 :height 2 :scale 1}))
(on (window/Frame seconds held)
  (update! frames inc)
  (update! events #(conj % (str "Frame " (pr-str held) " "
                                (and (> seconds 0.0) (< seconds 1.0)))))
  (if (= frames 3)
    (do @(console/print (string/join "\n" events)) @(window/close screen))
    unit))
(on (window/Press key)
  (update! events #(conj % (str "Press " (pr-str key)))))
(view screen
  (if (< frames 2) [0xff102030 0x00a0b0c0 0x7f000001] [1 2 3 4 5 6 7 8]))
|}

(* A view follows the names of all the program's files: here a module's,
   changed by its own ! function, from the window's handler. *)
let steps = {|(ns steps)
(let n::U32 0)
(fn step! [] (update! n inc))
|}

let several =
  {|(ns several (:require [vastra.window :as window] [steps]))
(let screen @(window/open {:title "several" :width 3 :height 2 :scale 1}))
(on (window/Frame _ _)
  (steps/step!)
  (if (= steps/n 3) @(window/close screen) unit))
(view screen [steps/n])
|}

let push ?(repeat = 0) typ code =
  let e = Sdl.Event.create () in
  Sdl.Event.(set e typ) typ;
  Sdl.Event.(set e keyboard_keycode) code;
  Sdl.Event.(set e keyboard_repeat) repeat;
  ignore (Sdl.push_event e)

let () =
  Unix.putenv "SDL_VIDEODRIVER" "dummy";
  Vastra_window.install ();
  let shown = ref [] in
  (Vastra_window.before_present :=
     fun renderer ->
       let pixels = Bigarray.(Array1.create int32 c_layout 6) in
       (* Here tsdl takes the row's length in bytes; update_texture in elements. *)
       let rgb = Some Sdl.Pixel.format_rgb888 in
       ignore (Sdl.render_read_pixels renderer None rgb pixels 12);
       shown := !shown @ [ Array.init 6 (fun i -> Int32.logand pixels.{i} 0xffffffl) ];
       let down = Sdl.Event.key_down and up = Sdl.Event.key_up in
       match List.length !shown with
       | 1 ->
           push down Sdl.K.left;
           push down Sdl.K.a;
           push down Sdl.K.left ~repeat:1;
           push down Sdl.K.lshift
       | 2 ->
           push up Sdl.K.a;
           push down Sdl.K.tab
       | _ -> ());
  let printed = ref [] in
  (Builtins.print := fun s -> printed := !printed @ [ s ]);
  let s = Session.create () in
  s.run_tasks <- true;
  (match Session.eval_source s program with
  | Ok _ -> ()
  | Error d -> check (Diagnostic.render d program "test") false);
  check "presses come before their frame; a repeat and a key without a name don't"
    (!printed
    = [
        "Frame [] true\n\
         Press ArrowLeft\n\
         Press (Char \"a\")\n\
         Frame [ArrowLeft (Char \"a\")] true\n\
         Press Tab\n\
         Frame [ArrowLeft Tab] true";
      ]);
  check "too few pixels leave black, extra ones are ignored, the alpha too"
    (!shown
    = [ [| 0x102030l; 0xa0b0c0l; 1l; 0l; 0l; 0l |]; [| 1l; 2l; 3l; 4l; 5l; 6l |] ]);
  Value.handlers := [];
  Value.views := [];
  shown := [];
  (Session.read := fun _ -> steps);
  let s = Session.create () in
  s.run_tasks <- true;
  (match Session.eval_source s several with
  | Ok _ -> ()
  | Error d -> check (Diagnostic.render d several "test") false);
  check "a window's view follows a module's names"
    (List.map (fun p -> p.(0)) !shown = [ 1l; 2l ]);
  if !failures > 0 then exit 1
