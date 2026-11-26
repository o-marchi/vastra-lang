(* vastra.js: Vastra in a web page. *)
let () =
  Vastra_web.install ();
  Vastra_web.run_page ();
  Live.connect ()
