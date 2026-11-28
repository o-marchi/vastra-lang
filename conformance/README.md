# Conformance suite

The executable specification of Vastra. Every implementation must produce
exactly the recorded output, errors and exit codes.

- `cases.txt` — small programs, each run as a file (`;;; file:`) or piped
  into the REPL (`;;; repl:`). Covers the reader, macros, analysis, type
  errors, runtime errors and REPL behaviour.
- `expected.json` — the recorded stdout, stderr and exit code of every case.
- `run.py` — runs the cases.

```bash
python3 -I conformance/run.py check BINARY        # does BINARY match the spec?
python3 -I conformance/run.py compare BIN1 BIN2   # do two implementations agree?
python3 -I conformance/run.py bless BINARY        # record BINARY's behaviour as the spec
python3 -I conformance/run.py compiled BINARY     # the same, on programs built with `vastra build`
python3 -I conformance/run.py compiled-js BINARY  # ... built with `vastra build --js`, compact and --readable, run with Node
```

From dune: `dune test` (interpreter), `dune build @compiled`,
`dune build @compiled-js`; the browser has its own checks (`dune build @browser`).
A few cases are interpreter-only or native-only; `run.py` lists them with
their reasons.

Add a case whenever a behaviour is decided or a bug is fixed. Re-blessing
changes the specification: review the diff of `expected.json` like a design
decision.
