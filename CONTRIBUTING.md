# Working on Vastra

## How we work

- **The conformance suite is the specification.** Every decided behaviour
  has a case in `conformance/cases.txt`, and its exact output is in
  `conformance/expected.json`. Changing that output (`run.py bless`) is a
  design change: review the diff and say why.
- **Rejection is tested as much as acceptance**, with the exact messages.
- **Code is written to be read.** The least code that does the job, nothing
  speculative; comments for the *why* and the surprising only; lines of at
  most 90 columns; small commits that say what to read.

## The code, in reading order

| File | What it does |
| --- | --- |
| `lib/reader.ml` | Text → forms, each with its byte span |
| `lib/diagnostic.ml` | The one error type, its rendering, suggestions and `try:` fixes |
| `lib/why.txt` | The long form of each rule an error states, which `:why` shows |
| `lib/expand.ml` | Macro expansion (macros are Vastra functions, from the session) |
| `lib/ast.ml`, `lib/analyze.ml` | Forms → syntax tree; special forms and their shape |
| `lib/lift.ml` | `@`: each await pulled out into a chain of tasks |
| `lib/pretty.ml` | Values and types laid out for a width, or on one line |
| `lib/types.ml`, `lib/infer.ml` | Types; Hindley–Milner inference with rows and constraints |
| `lib/exhaustive.ml` | Missing and unreachable `match` clauses |
| `lib/once.ml` | A name holding a buffer is used once on each path |
| `lib/clock.ml` | The clock and the native timers, which the interpreter, built programs and a window's frames run |
| `lib/value.ml`, `lib/builtins.ml`, `lib/eval.ml` | Values, natives (stopping tasks), the interpreter |
| `lib/session.ml` | A submission end to end: scopes, modules, macros, redefinition |
| `lib/prelude.vas`, `lib/stdlib/*.vas` | The core and the standard library, in Vastra |
| `lib/compile.ml`, `lib/rt.ml` | `vastra build`: Vastra → OCaml, and its runtime |
| `bin/main.ml`, `bin/repl.ml` | The `vastra` command and the REPL |
| `bin/terminal/` | The REPL's terminal: `term.ml` keys and the terminal's answers, `look.ml` styled rows, `theme.ml` the colours for the terminal's ground, `syntax.ml` and `input.ml` the text being typed and the history, `area.ml` the live area, `waiting.ml` the waiting line, `screen.ml` where the transcript and the live area go, `show.ml` results laid out by their shape and `explore.ml` opening a value |
| `bin/serve.ml`, `web/live.ml` | `vastra serve`, and its side in the page: serving, reloading on save, the REPL into the page |
| `web/lib/vastra_web.ml` | The browser: JavaScript calls, rendering, events, HTTP, recording and replaying |
| `lib/window/vastra_window.ml` | A window, through tsdl: a library of its own, which `vastra.js` doesn't link |

## Building and testing

Zarith needs `libgmp-dev`; tsdl needs `libsdl2-dev` and `libffi-dev`.

```bash
opam switch create . ocaml-base-compiler.5.4.1 --no-install   # once
opam install . --deps-only
eval $(opam env --switch=. --set-switch)                       # each shell

dune build                # the vastra command (vastra.js inside), the library
dune exec vastra -- ARGS  # this build's vastra
dune test                 # conformance, interpreter
dune build @compiled      # conformance, programs compiled natively
dune build @compiled-js   # conformance, programs compiled to JavaScript (Node)
dune build @browser       # headless Chrome, on pages vastra serve serves: the
                          # counter, fetch, the REPL page, editing a running page
```

`dune test` also runs `test/terminal_test.ml`, on the pure parts of the
REPL's terminal, and `test/window_test.ml`, a window program on SDL's dummy
video driver.

`vastra build` links the installed `vastra` library: `dune install`, or
`export OCAMLPATH=$PWD/_build/install/default/lib` after `dune build @install`.
