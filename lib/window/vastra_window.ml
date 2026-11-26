(* vastra.window: a program in a window, its handlers and its view, run
   as a page runs one, through tsdl. *)

open Tsdl
open Vastra
open Value

let wrong () = raise (Internal "vastra.window")

(* Keys as the web names them, from SDL's key codes: a key that types a
   character has it, unshifted, as its code. Other keys give no events. *)
let names =
  Sdl.K.
    [
      (left, "ArrowLeft"); (right, "ArrowRight"); (up, "ArrowUp"); (down, "ArrowDown");
      (escape, "Escape"); (tab, "Tab"); (return, "Enter");
    ]

let key code =
  match List.assoc_opt code names with
  | Some name -> Some (Ctor ("vastra.window/" ^ name, []))
  | None when code >= 32 && code <> 127 && Uchar.is_valid code ->
      let b = Buffer.create 4 in
      Buffer.add_utf_8_uchar b (Uchar.of_int code);
      Some (Ctor ("vastra.window/Char", [ Str (Buffer.contents b) ]))
  | None -> None

(* An open window: what draws its picture, and whether it is still open. *)
type screen = {
  window : Sdl.window;
  renderer : Sdl.renderer;
  texture : Sdl.texture;
  width : int;
  height : int;
  mutable shown : bool;
}

type Value.opaque += Screen of screen

(* Called before each frame is shown, with its renderer: a test pushes events
   and reads the pixels back there. *)
let before_present : (Sdl.renderer -> unit) ref = ref ignore

(* A window [scale] times the picture's size, which can be resized: the picture
   keeps its proportions (SDL's logical size). It is shown at the display's
   refresh. RGB888 ignores the alpha. *)
let open_window title width height scale =
  let ( let* ) = Result.bind in
  let* () = Sdl.init Sdl.Init.video in
  let centered = Sdl.Window.pos_centered in
  let* window =
    Sdl.create_window title ~x:centered ~y:centered ~w:(width * scale) ~h:(height * scale)
      Sdl.Window.resizable
  in
  let* renderer = Sdl.create_renderer ~flags:Sdl.Renderer.presentvsync window in
  let* () = Sdl.render_set_logical_size renderer width height in
  let* texture =
    Sdl.create_texture renderer Sdl.Pixel.format_rgb888 Sdl.Texture.access_streaming
      ~w:width ~h:height
  in
  Ok { window; renderer; texture; width; height; shown = true }

(* Too few pixels leave the rest black, and extra ones are ignored. *)
let fill pixels = function
  | Vector v ->
      let n = min (Array.length v) (Bigarray.Array1.dim pixels) in
      for i = 0 to n - 1 do
        pixels.{i} <- (match v.(i) with Fixed (_, x) -> x | _ -> wrong ())
      done;
      Bigarray.Array1.(fill (sub pixels n (dim pixels - n)) 0l)
  | _ -> wrong ()

(* The window's frames, once the file that opened it has run: each
   frame, at the display's refresh, the timers that are due run, the
   Press events that came in and then the Frame go to the handlers, and the
   window's view is shown. They run until the window closes. *)
let frames sc () =
  let event = Sdl.Event.create () and held = ref [] in
  let code () = Sdl.Event.(get event keyboard_keycode) in
  let pixels = Bigarray.(Array1.create int32 c_layout (sc.width * sc.height)) in
  let frequency = Int64.to_float (Sdl.get_performance_frequency ()) in
  let deliver e = if sc.shown then Value.deliver ~window:true e in
  (* The window's program ends with it: the timers waiting go, those set
     at the REPL's prompt too. *)
  Fun.protect
    ~finally:(fun () ->
      Sdl.destroy_renderer sc.renderer;
      Sdl.destroy_window sc.window;
      Sdl.quit ();
      Clock.clear ())
    (fun () ->
      let last = ref (Sdl.get_performance_counter ()) in
      while sc.shown do
        Clock.run_due ();
        (* Keys held are followed from their events, as a page must: a pushed
           event counts, and SDL lets go of every key when the window loses
           the keyboard. *)
        while Sdl.poll_event (Some event) do
          match Sdl.Event.(enum (get event typ)) with
          | `Quit -> sc.shown <- false
          | `Key_down when Sdl.Event.(get event keyboard_repeat) = 0 ->
              let c = code () in
              held := List.filter (( <> ) c) !held @ [ c ];
              Option.iter (fun k -> deliver (Ctor ("vastra.window/Press", [ k ]))) (key c)
          | `Key_up -> held := List.filter (( <> ) (code ())) !held
          | _ -> ()
        done;
        let now = Sdl.get_performance_counter () in
        let seconds = Int64.(to_float (sub now !last)) /. frequency in
        last := now;
        let keys = Vector (Array.of_list (List.filter_map key !held)) in
        deliver (Ctor ("vastra.window/Frame", [ Float seconds; keys ]));
        let mine (v : Value.view) =
          match v.place with Opaque (Screen s) -> s == sc | _ -> false
        in
        match List.find_opt mine !Value.views with
        | Some v when sc.shown ->
            fill pixels (!apply v.draw []);
            ignore (Sdl.update_texture sc.texture None pixels sc.width);
            ignore (Sdl.render_clear sc.renderer);
            ignore (Sdl.render_copy sc.renderer sc.texture);
            !before_present sc.renderer;
            Sdl.render_present sc.renderer
        | _ -> ()
      done)

let open_ = function
  | [ Record config ] ->
      Task
        (fun k ->
          let field key = List.assoc key config in
          let size key =
            match field key with Int n -> max 1 (Builtins.small n) | _ -> wrong ()
          in
          let title = match field "title" with Str s -> s | _ -> wrong () in
          match open_window title (size "width") (size "height") (size "scale") with
          | Error (`Msg m) ->
              Sdl.quit ();
              k (Error (Ctor ("vastra.window/CannotOpen", [ Str m ])))
          | Ok sc ->
              Value.loop := frames sc;
              k (Ok (Opaque (Screen sc))))
  | _ -> wrong ()

(* Provides vastra.window's natives. *)
let install () =
  Builtins.extra :=
    [
      ("vastra.window/open", Builtin { builtin_name = "open"; run = open_ });
      ( "vastra.window/close",
        Builtin
          {
            builtin_name = "close";
            run =
              (function
              | [ Opaque (Screen sc) ] ->
                  Task
                    (fun k ->
                      sc.shown <- false;
                      k (Ok Unit))
              | _ -> wrong ());
          } );
    ]
