<img src=".github/mark.svg" alt="" width="96">

# Vastra

Hi, this is Vastra, an interactive, safe and fast Lisp.

This is a representation of what I believe programming languages should strive for:

**1. Interactive**

In my opinion, the best way to program is having a conversation with your
program while it runs.

Following the Lisp tradition, this language includes a REPL.
Save a file, and the running program gets the change without restarting or
losing its state. In the REPL you look inside it and try things, and it checks
what you type while you type.

**2. No runtime errors\***

Before it runs, the language tells you when you write code that can break.
Errors from outside (a missing file, a failed request, bad input) come as
values your program handles.

We don't have `nil` values. Every time a value might not exist, you say what
the program should do in that case.

\*Almost. No language can protect you from running out of memory, a loop that
never ends, recursion that goes too deep, or the browser or the operating
system failing.
For anything else, if Vastra accepted your program, a runtime error is a bug in
Vastra itself.

**3. Fast**

Ok, it's not fast yet. The plan is pages about as fast as React's on the web,
and programs close to OCaml's on your computer. For now the focus is a working
language first; optimizing comes later.

## Don't use this in production

Vastra is incomplete, and I'm actively working on it, so the syntax and the
libraries will still change. It's implemented in OCaml, and programs run
interpreted, compiled to native code, or in web pages with JavaScript.

## How to use

There's no installer yet: build `vastra` from this repository, as
`CONTRIBUTING.md` describes. Then:

```bash
vastra                    # the REPL
vastra FILE               # run FILE, printing each result and its type
vastra run FILE ARGS      # run FILE as a program
vastra build FILE         # compile it (--js: to JavaScript)
vastra serve FOLDER       # a live page, with a REPL into it
```

## License

MIT.
