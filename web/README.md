# Vastra in the browser

`vastra.js` is the Vastra implementation compiled to JavaScript with
js_of_ocaml (`web/lib/vastra_web.ml` adds what only a browser has: JavaScript
calls, rendering, events and HTTP; `live.ml` is the page's side of `vastra
serve`). The `vastra` command carries it, and `vastra serve` gives it to every
page it serves:

```bash
vastra serve web/test/fixtures/counter  # a counter: http://localhost:8000
vastra serve web                        # the REPL page: http://localhost:8000/repl.html
```

- `test/check.mjs` drives Chrome through the DevTools protocol, on pages that
  `vastra serve` serves: a counter (also with storage blocked, and compiled
  with `vastra build --js`), a program with a type error, fetching and
  decoding JSON (also from a program built for Node), the REPL page, a page's
  state changed from the prompt and recorded, a page's REPL into itself, and
  `vastra serve` itself (paths outside the folder, editing the counter while it runs, the
  terminal's REPL). `CONTRIBUTING.md` says how to run it.
- `test/fixtures/` holds the test pages.
