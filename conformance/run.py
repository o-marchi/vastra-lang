#!/usr/bin/env python3
"""Vastra conformance suite: the executable specification of the language.

Usage:
    python3 -I conformance/run.py check BINARY       compare BINARY with expected.json
    python3 -I conformance/run.py bless BINARY       record BINARY's behaviour as expected
    python3 -I conformance/run.py compare BIN1 BIN2  compare two implementations directly
    python3 -I conformance/run.py compiled BINARY    check programs compiled with `vastra build`
                                                     (needs the vastra library: OCAMLPATH)
    python3 -I conformance/run.py compiled-js BINARY check programs compiled with `vastra build --js`,
                                                     run with Node

Options:
    --verbose    list every case, not only failures

Cases come from conformance/cases.txt.
A case is a file (`;;; file: NAME`), a REPL
session (`;;; repl: NAME`), or a program run (`;;; run: NAME`, whose first
line holds the arguments of `vastra run`). A case can hold extra files (such
as modules it requires): each starts at a line `;;;; file: PATH`.
Each case is run as a file (`vastra NAME.vas`) or piped into the REPL
(`vastra < NAME.vas`), in a temporary directory, so paths in error messages are
stable. stdout, stderr and the exit code must match byte for byte. The REPL
banner (the first line of a REPL session), which names the implementation, is
excluded.

Exits with status 0 if every case matches.
"""

import json
import re
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
EXPECTED = os.path.join(HERE, "expected.json")

# No case opens a window on the screen: SDL's dummy video driver runs them.
os.environ["SDL_VIDEODRIVER"] = "dummy"


def parse_cases(path):
    """Yields (mode, name, source) for each case in a cases file."""
    mode = name = None
    lines = []
    with open(path, encoding="utf-8") as f:
        for line in f:
            if line[:10] in (";;; file: ", ";;; repl: ") or line.startswith(";;; run: "):
                if mode:
                    yield mode, name, "".join(lines)
                mode, _, name = line[4:].partition(": ")
                name = name.strip()
                lines = []
            elif mode:
                lines.append(line)
    if mode:
        yield mode, name, "".join(lines)


def all_cases():
    cases = list(parse_cases(os.path.join(HERE, "cases.txt")))
    names = [name for _, name, _ in cases]
    duplicates = {n for n in names if names.count(n) > 1}
    if duplicates:
        sys.exit(f"duplicate case names: {sorted(duplicates)}")
    return cases


def write_files(directory, source):
    """Writes a case's extra modules; returns the main source."""
    parts = re.split(r"\n;;;; (?:file|module): ", "\n" + source)
    parts[0] = parts[0][1:]
    for part in parts[1:]:
        path, _, text = part.partition("\n")
        full = os.path.join(directory, path.strip())
        os.makedirs(os.path.dirname(full), exist_ok=True)
        with open(full, "w", encoding="utf-8") as f:
            f.write(text)
    return parts[0]


def outcome(result):
    return {"exit": result.returncode, "stdout": result.stdout.decode("utf-8", "replace"),
            "stderr": result.stderr.decode("utf-8", "replace")}


def run_compiled(binary, mode, name, source, workdir, js=False):
    """Builds a file or run case with `vastra build`, then runs the program."""
    directory = os.path.join(workdir, name.replace("/", "_"))
    os.makedirs(directory, exist_ok=True)
    source = write_files(directory, source)
    if mode == "run":
        args = source.split("\n", 1)[0].split()
    else:
        args = [name.replace("/", "_") + ".vas"]
        with open(os.path.join(directory, args[0]), "w", encoding="utf-8") as f:
            f.write(source)
    program = os.path.join(workdir, name.replace("/", "_") + (".js" if js else ".exe"))
    flags = (["--show"] if mode == "file" else []) + (["--js"] if js else [])
    built = subprocess.run([binary, "build"] + flags + [args[0], "-o", program], cwd=directory,
                           capture_output=True, timeout=300)
    if built.returncode != 0:
        if mode == "run" and b"cannot read" in built.stderr:
            return outcome(built)
        return outcome(built)
    command = (["node", program] if js else [program]) + args[1:]
    return outcome(subprocess.run(command, cwd=directory, capture_output=True, timeout=60))


def run(binary, mode, name, source, workdir):
    """Runs one case; returns {"exit", "stdout", "stderr"}."""
    if mode == "run":
        workdir = os.path.join(workdir, name)
        os.makedirs(workdir, exist_ok=True)
        source = write_files(workdir, source)
        args = source.split("\n", 1)[0].split()
        result = subprocess.run([binary, "run"] + args, cwd=workdir, capture_output=True, timeout=60)
        return {"exit": result.returncode, "stdout": result.stdout.decode("utf-8", "replace"),
                "stderr": result.stderr.decode("utf-8", "replace")}
    filename = name.replace("/", "_") + ".vas"
    workdir = os.path.join(workdir, filename[:-4])
    os.makedirs(workdir, exist_ok=True)
    source = write_files(workdir, source)
    with open(os.path.join(workdir, filename), "w", encoding="utf-8") as f:
        f.write(source)
    if mode == "file":
        result = subprocess.run([binary, filename], cwd=workdir, capture_output=True, timeout=60)
    else:
        with open(os.path.join(workdir, filename), "rb") as stdin:
            result = subprocess.run([binary], cwd=workdir, stdin=stdin, capture_output=True, timeout=60)
    stdout = result.stdout.decode("utf-8", "replace")
    if mode == "repl":
        # Drop the banner, which names the implementation.
        stdout = stdout.split("\n", 1)[1] if "\n" in stdout else ""
    return {"exit": result.returncode, "stdout": stdout, "stderr": result.stderr.decode("utf-8", "replace")}


def report(name, mode, first, second, labels):
    print(f"  DIFF  {mode} {name}")
    for key in ("exit", "stdout", "stderr"):
        if first[key] != second[key]:
            print(f"    {key}:\n      {labels[0]}: {first[key]!r}\n      {labels[1]}: {second[key]!r}")


# Behaviours that differ by design in compiled programs.
INTERPRETER_ONLY = {
    "deep-recursion-limit",  # compiled code has no depth counter: OCaml's stack is the limit
    "quote-and-quasiquote",  # quasiquote evaluated at run time is not compiled yet
}


# Programs whose modules run on some platforms only: built for JavaScript,
# they give another answer. Pages check theirs (`dune build @browser`).
NATIVE_ONLY = {
    "browser-modules-need-the-browser",  # built for JavaScript, browser modules are allowed
    "storage-needs-the-browser",
    "native-modules-run-natively",  # built for JavaScript, the :require is refused
    "es-modules-need-javascript",  # built for JavaScript, the module is imported
    "a-window-runs-frames-until-it-closes",
    "window-events-need-no-on-each",
    "window-events-cannot-be-sent",
}


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    verbose = "--verbose" in sys.argv
    if not args or args[0] not in ("check", "bless", "compare", "compiled", "compiled-js") or len(args) != (3 if args[0] == "compare" else 2):
        print(__doc__)
        return 2
    command, binaries = args[0], [os.path.abspath(b) for b in args[1:]]
    cases = all_cases()

    with tempfile.TemporaryDirectory(prefix="vastra-conformance-") as workdir:
        if command == "bless":
            expected = {name: dict(mode=mode, **run(binaries[0], mode, name, source, workdir)) for mode, name, source in cases}
            with open(EXPECTED, "w", encoding="utf-8") as f:
                json.dump(expected, f, indent=2, ensure_ascii=False, sort_keys=True)
                f.write("\n")
            print(f"recorded {len(expected)} cases in {os.path.relpath(EXPECTED, ROOT)}")
            return 0

        if command in ("check", "compiled", "compiled-js"):
            with open(EXPECTED, encoding="utf-8") as f:
                expected = json.load(f)
            missing = [name for _, name, _ in cases if name not in expected]
            if missing:
                print(f"no expected output for: {', '.join(missing)} (run `bless` after reviewing)")

        failures = 0
        if command.startswith("compiled"):
            # Compiled programs have no REPL, and these behaviours belong to the interpreter.
            skip = INTERPRETER_ONLY | (NATIVE_ONLY if command == "compiled-js" else set())
            cases = [c for c in cases if c[0] != "repl" and c[1] not in skip]
        for mode, name, source in cases:
            if command.startswith("compiled"):
                want = {k: expected[name][k] for k in ("exit", "stdout", "stderr")}
                got = run_compiled(binaries[0], mode, name, source, workdir, js=command == "compiled-js")
                labels = ("expected", "compiled")
            elif command == "check":
                if name not in expected:
                    failures += 1
                    continue
                want = {k: expected[name][k] for k in ("exit", "stdout", "stderr")}
                got = run(binaries[0], mode, name, source, workdir)
                labels = ("expected", "actual  ")
            else:
                want = run(binaries[0], mode, name, source, workdir)
                got = run(binaries[1], mode, name, source, workdir)
                labels = ("first ", "second")
            if want == got:
                if verbose:
                    print(f"  ok    {mode} {name}")
            else:
                failures += 1
                report(name, mode, want, got, labels)

    print(f"{len(cases) - failures}/{len(cases)} cases match")
    return 0 if failures == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
