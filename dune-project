(lang dune 3.0)

(generate_opam_files true)

(package
 (name vastra)
 (synopsis "An interactive, safe and fast Lisp")
 (license MIT)
 (depends ocaml dune zarith tiny_httpd js_of_ocaml js_of_ocaml-ppx zarith_stubs_js tsdl
  mtime))
