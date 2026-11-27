(* vastra.js: Vastra in a web page. *)
let () =
  Vastra_web.install ();
  Page_session.install ();
  Page_session.run_page ();
  Live.connect ()
