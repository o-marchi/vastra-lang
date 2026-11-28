// What a built program takes from Vastra, one function per paragraph: the
// printer copies only those a program uses, and those they use.

// An Int is a number while it is a safe integer, and a BigInt past that:
// one value, one form, so === and < work on Ints as they come.
function add(a, b) {
  if (typeof a === "number" && typeof b === "number") {
    const r = a + b;
    if (Number.isSafeInteger(r)) return r;
  }
  return whole(BigInt(a) + BigInt(b));
}

function sub(a, b) {
  if (typeof a === "number" && typeof b === "number") {
    const r = a - b;
    if (Number.isSafeInteger(r)) return r;
  }
  return whole(BigInt(a) - BigInt(b));
}

function mul(a, b) {
  if (typeof a === "number" && typeof b === "number") {
    const r = a * b;
    if (Number.isSafeInteger(r)) return r;
  }
  return whole(BigInt(a) * BigInt(b));
}

// A BigInt that fits back as a safe integer becomes a number.
function whole(n) {
  return n >= -9007199254740991n && n <= 9007199254740991n ? Number(n) : n;
}

// A map as the REPL prints it, its keys in its own order, each by its type.
function showRecord(r, shows) {
  return "{" + Object.keys(r).map((k) => ":" + k + " " + shows[k](r[k])).join(", ") + "}";
}

// A String as Vastra code writes it: quoted, with ", \, newline and tab escaped.
function quote(s) {
  return "\"" + s.split("\\").join("\\\\").split("\"").join("\\\"").split("\n").join("\\n").split("\t").join("\\t") + "\"";
}

// The shortest text that reads back as the same Float, as C's %g writes it.
function showFloat(x) {
  if (Number.isNaN(x)) return "NaN";
  if (Number.isInteger(x) && Math.abs(x) < 1e15) return (Object.is(x, -0) ? "-0" : x.toFixed(0)) + ".0";
  if (!Number.isFinite(x)) return x > 0 ? "Infinity" : "-Infinity";
  const trim = (s) => (s.includes(".") ? s.replace(/\.?0+$/, "") : s);
  for (const digits of [15, 16, 17]) {
    const [mantissa, exponent] = x.toExponential(digits - 1).split("e");
    if (Number(mantissa + "e" + exponent) !== x) continue;
    const e = Number(exponent);
    if (e >= -4 && e < digits) return trim(x.toFixed(digits - 1 - e));
    return trim(mantissa) + "e" + (e < 0 ? "-" : "+") + String(Math.abs(e)).padStart(2, "0");
  }
}

// Whether two values are the same, all the way down.
function equal(a, b) {
  if (a === b) return true;
  if (typeof a !== "object" || typeof b !== "object") return false;
  const ka = Object.keys(a), kb = Object.keys(b);
  return ka.length === kb.length && ka.every((k) => equal(a[k], b[k]));
}

// [start, start + 1, … end - 1]
function range(start, end) {
  const out = [];
  for (let i = start; i < end; i++) out.push(i);
  return out;
}

function first(xs) {
  return xs.length > 0 ? Some(xs[0]) : None;
}

// What a vector or a buffer holds at i, as an Option.
function at(xs, i) {
  return i >= 0 && i < xs.length ? Some(xs[i]) : None;
}

// A buffer with v at i, changed in place: no one else holds it. At its end, i
// makes it one longer, as set does; past that, it stays as it is.
function put(xs, i, v) {
  if (i >= 0 && i < xs.length) {
    xs[i] = v;
    return xs;
  }
  if (i !== xs.length) return xs;
  if (Array.isArray(xs)) {
    xs.push(v);
    return xs;
  }
  const grown = new xs.constructor(xs.length + 1);
  grown.set(xs);
  grown[xs.length] = v;
  return grown;
}

// A call handed back. JavaScript grows its stack with every call, where
// Vastra doesn't for a function's last one, so a function ending with a call
// to a function the printer can't name gives back what to call instead.
// Whoever uses the result settles it: one call at a time, the stack flat.
function next(f, args) {
  return new Next(f, args);
}

function Next(f, args) {
  this.f = f;
  this.args = args;
}

function settle(result) {
  while (result instanceof Next) result = result.f(...result.args);
  return result;
}

// f, for code that calls it and uses what it gives, like map.
function settled(f) {
  return (...args) => settle(f(...args));
}

// Typed arrays the program has let go: nothing holds them, so the next copy of
// the same kind and length can be written into one of them. A frame made every
// round then costs a copy, not an allocation. A few at most.
const spares = [];

function spare(b) {
  spares.push(b);
  if (spares.length > 4) spares.shift();
}

// A copy of the typed array xs, in a spare when there is one.
function copied(xs) {
  const i = spares.findIndex((b) => b.constructor === xs.constructor && b.length === xs.length);
  if (i < 0) return xs.slice();
  const b = spares.splice(i, 1)[0];
  b.set(xs);
  return b;
}

function stringToInt(s) {
  return /^-?[0-9]+$/.test(s) ? Some(whole(BigInt(s))) : None;
}

// Html's children: a String is text, a vector its elements.
function htmlChild(c) {
  if (typeof c === "string") return [Text(c)];
  return Array.isArray(c) ? c.flatMap(htmlChild) : [c];
}

// A page's handlers, by the constructor of the message each takes.
const handlers = [];

function on(tag, handle) {
  handlers.push({ tag: tag, handle: handle });
}

// A constructor's values: {tag, 0: a, 1: b} gives [a, b].
function values(c) {
  const out = [];
  for (let i = 0; i in c; i++) out.push(c[i]);
  return out;
}

// A message goes to the first handler that takes it. Then the messages it
// sent, and the views draw again; the same after any task it started.
function dispatch(message) {
  const h = handlers.find((h) => h.tag === message.tag);
  if (h) {
    const task = h.handle(...values(message));
    if (task) run(task, program, handled);
  }
  handleSent();
  redraw();
}

// The messages send! gave. Each waits for the handler running to end, or,
// when none is running, for the next turn.
const outbox = [];

function send(message) {
  outbox.push(message);
  setTimeout(handleSent, 0);
}

function handleSent() {
  if (outbox.length > 0) dispatch(outbox.shift());
}

// What each view shows at its place: drawn now, and again after changes.
const views = [];

function view(place, draw) {
  views.push({ place: place, draw: draw, node: null, html: null });
  redraw();
}

function redraw() {
  // Without a page, as in Node, a view has nowhere to draw.
  if (typeof document === "undefined") return;
  for (const v of views) {
    const html = v.draw();
    if (v.node) v.node = patch(v.node, v.html, html);
    else document.querySelector(v.place).replaceChildren((v.node = create(html)));
    v.html = html;
  }
}

// An Element is {tag, 0: name, 1: attributes, 2: children}; a Text, {tag, 0: text}.
function create(html) {
  if (html.tag === "Text") return document.createTextNode(html[0]);
  if (html.tag !== "Element") return document.createComment("nothing");
  const element = document.createElement(html[0]);
  setAttributes(element, [], html[1]);
  for (const child of html[2]) element.appendChild(create(child));
  return element;
}

// Changes [node], drawn from [old], to show [html]; only what differs.
function patch(node, old, html) {
  if (old.tag !== html.tag || (html.tag === "Element" && old[0] !== html[0])) {
    const fresh = create(html);
    node.replaceWith(fresh);
    return fresh;
  }
  if (html.tag === "Text" && old[0] !== html[0]) node.nodeValue = html[0];
  if (html.tag !== "Element") return node;
  setAttributes(node, old[1], html[1]);
  const before = old[2], after = html[2], kids = [...node.childNodes];
  after.forEach((child, i) => (i < before.length ? patch(kids[i], before[i], child) : node.appendChild(create(child))));
  kids.slice(after.length).forEach((kid) => kid.remove());
  return node;
}

function setAttributes(element, old, attributes) {
  const named = (as) => as.filter((a) => a.tag === "Attribute" || a.tag === "Flag").map((a) => a[0]);
  const now = named(attributes);
  for (const name of named(old)) if (!now.includes(name)) element.removeAttribute(name);
  element.onclick = element.oninput = element.onsubmit = null;
  for (const attribute of attributes) {
    const tag = attribute.tag, a = attribute[0], b = attribute[1];
    if (tag === "Attribute" && a === "value") {
      if (element.value !== b) element.value = b; // the live value, to keep the cursor
    } else if (tag === "Attribute") element.setAttribute(a, b);
    else if (tag === "Flag") element[a] = b;
    else if (tag === "OnClick") element.onclick = () => dispatch(a);
    else if (tag === "OnInput") element.oninput = () => dispatch(a(element.value));
    else if (tag === "OnSubmit") element.onsubmit = (e) => (e.preventDefault(), dispatch(a));
  }
}

// A Float's whole part, toward zero, within [lo, hi]: NaN and the infinities
// give 0, as vastra run gives them.
function clampWhole(x, lo, hi) {
  if (!Number.isFinite(x)) return 0;
  return x <= lo ? lo : x >= hi ? hi : Math.trunc(x);
}

// An Int's low 32 bits, read unsigned.
function lowBits(x) {
  return typeof x === "bigint" ? Number(BigInt.asUintN(32, x)) : x >>> 0;
}

// A Float's whole part as an Int: the infinities and NaN give 0. Within 32
// bits it is x | 0, which an engine keeps as a small integer from then on.
function wholePart(x) {
  if (x >= -2147483648 && x < 2147483648) return x | 0;
  if (!Number.isFinite(x)) return 0;
  const t = Math.trunc(x);
  return Number.isSafeInteger(t) ? t : BigInt(t);
}

// Floats ignore NaN, and -0.0 is below 0.0, as C23's fmaximum_num.
function minFloat(a, b) {
  return a !== a ? b : b !== b ? a : Math.min(a, b);
}

function maxFloat(a, b) {
  return a !== a ? b : b !== b ? a : Math.max(a, b);
}

function least(a, b) {
  return a <= b ? a : b;
}

function most(a, b) {
  return a >= b ? a : b;
}

// mod: never negative, whatever the signs; b is not 0.
function remainder(a, b) {
  if (typeof a === "number" && typeof b === "number") {
    const r = a % b;
    return r < 0 ? r + Math.abs(b) : r;
  }
  const r = BigInt(a) % BigInt(b);
  return whole(r < 0n ? r + (BigInt(b) < 0n ? -BigInt(b) : BigInt(b)) : r);
}

// quot: toward zero; b is not 0.
function quotient(a, b) {
  if (typeof a === "number" && typeof b === "number" && Math.abs(a) <= 2147483647) return Math.trunc(a / b);
  return whole(BigInt(a) / BigInt(b));
}

// quot of two signed numbers [bits] wide, the lowest over -1 wrapping, as in C.
function quotSigned(a, b, bits) {
  return b == 0 ? None : Some((Math.trunc(a / b) << (32 - bits)) >> (32 - bits));
}

// A fixed-width number's bits in hexadecimal, as many digits as they take.
function hex(x, bits) {
  const kept = bits === 32 ? x >>> 0 : x & ((1 << bits) - 1);
  return kept.toString(16).padStart(bits / 4, "0");
}

// An Int in hexadecimal: -255 is -ff.
function stringHex(x) {
  return x.toString(16);
}

// A task's failure, thrown through the tasks waiting for it until one takes it.
function Failure(error) {
  this.error = error;
}

// A task is a generator function: each task it waits for, it yields, and
// run runs it. A task value is a function of no arguments that gives one.
function started(t) {
  return typeof t === "function" ? t() : t;
}

// A wait for something outside the program: start begins it, given what to
// call when it ends, and gives what calls it off. A Promise yielded is one.
function Wait(start) {
  this.start = start;
}

// A running task, which stop! stops: what it waits for is called off, and it
// never goes on. A stopped one is a running task that has ended.
function Running(stopped) {
  this.stopped = stopped;
  this.waits = new Set();
}

// The program's running, which never stops.
const program = new Running(false);

// The running whose code runs now: the program's, unless later, task/race or
// task/first-of started one.
let current = program;

// Runs task t in running r, as vastra run does: on and on until it waits for
// something outside the program, so each task waits only there. done gets
// (true, value) or (false, what was thrown) when it ends. The tasks waiting
// for others are a list here, so a long chain of them takes no stack.
function run(t, r, done) {
  const tasks = [started(t)];
  const go = (ok, v) => {
    for (;;) {
      const outer = current;
      current = r;
      let step = null;
      try {
        const task = tasks[tasks.length - 1];
        step = ok ? task.next(v) : task.throw(v);
      } catch (x) {
        v = x;
      }
      current = outer;
      if (step === null || step.done) {
        tasks.pop();
        ok = step !== null;
        if (ok) v = step.value;
        if (tasks.length === 0) return done(ok, v);
      } else if (typeof step.value.next === "function") {
        tasks.push(step.value);
        ok = true;
        v = undefined;
      } else return wait(r, step.value, go);
    }
  };
  go(true, undefined);
}

// r waits for w; when it ends, go goes on, unless r stopped meanwhile.
function wait(r, w, go) {
  if (r.stopped) return;
  const start = w instanceof Wait ? w.start : (ended) => (w.then((v) => ended(true, v), (x) => ended(false, x)), () => {});
  const cancel = start((ok, v) => {
    r.waits.delete(cancel);
    if (!r.stopped) go(ok, v);
  });
  r.waits.add(cancel);
}

// Stopping one that has ended, or stopped, does nothing.
function stop(r) {
  if (r.stopped) return;
  r.stopped = true;
  const cancels = [...r.waits];
  r.waits.clear();
  for (const cancel of cancels) cancel();
}

const taskEnded = new Running(true);

// What a task's failure held; anything else thrown is a fault, thrown on.
function caught(x) {
  if (x instanceof Failure) return x.error;
  throw x;
}

function* taskSucceed(value) {
  return value;
}

function* taskFail(error) {
  throw new Failure(error);
}

function* taskFromResult(r) {
  if (r.tag === "Ok") return r[0];
  throw new Failure(r[0]);
}

function* taskMap(t, f) {
  return f(yield started(t));
}

function* taskMapErr(t, f) {
  try {
    return yield started(t);
  } catch (x) {
    throw new Failure(f(caught(x)));
  }
}

function* taskRecover(t, f) {
  try {
    return yield started(t);
  } catch (x) {
    return yield started(f(caught(x)));
  }
}

// One at a time, in order; the first failure ends it.
function* taskAll(ts) {
  const out = [];
  for (const t of ts) out.push(yield started(t));
  return out;
}

// Each task starts when the one before has ended or waits for something
// outside the program, so tasks that wait, wait together. It gives every
// outcome, in the tasks' order.
function* taskConcurrent(ts) {
  const outcomes = [];
  let left = ts.length, back = null;
  ts.forEach((t, i) =>
    run(t, current, (ok, v) => {
      outcomes[i] = ok ? Ok(v) : Err(caught(v));
      if (--left === 0 && back) back(true, outcomes);
    }),
  );
  return left === 0 ? outcomes : yield new Wait((ended) => ((back = ended), () => {}));
}

// The tasks start in order, each in a running of its own; the first to end
// gives the outcome, and the others stop. One that ends at once leaves the
// rest unstarted, so in a tie the first written wins.
function* taskRace(...ts) {
  const runnings = [];
  let outcome = null, back = null;
  const end = (ok, v) => {
    if (outcome) return;
    outcome = [ok, v];
    runnings.forEach(stop);
    if (back) back(ok, v);
  };
  for (const t of ts) {
    if (outcome) break;
    runnings.push(new Running(false));
    run(t, runnings[runnings.length - 1], end);
  }
  if (outcome === null) return yield new Wait((ended) => ((back = ended), () => runnings.forEach(stop)));
  if (outcome[0]) return outcome[1];
  throw outcome[1];
}

function* taskFirstOf(ts) {
  return ts.length === 0 ? None : Some(yield taskRace(...ts));
}

// The task runs in a running of its own, which only stop! or the program's
// end stops. When it ends, the clauses get its outcome, and run as the
// program's, as a handler does.
function* macroLater(t, clauses) {
  const r = new Running(false);
  run(t, r, (ok, v) => {
    const outcome = ok ? Ok(v) : Err(caught(v));
    if (clauses) run(clauses(outcome), program, handled);
  });
  return r;
}

function* macroLaterDropping(t) {
  return yield macroLater(t);
}

// After a handler's task, or later's clauses: the messages they sent, then
// the views draw again.
function handled(ok, v) {
  if (!ok) throw v;
  handleSent();
  redraw();
}

// The first top-level task that failed with nothing taking the failure, as
// vastra run says it: told when the program ends, which then exits with 1.
const untaken = [];

function untake(x, before, show, after) {
  if (!(x instanceof Failure)) throw x;
  if (untaken.length === 0) untaken.push(before + show(x.error) + after);
}

function finish() {
  if (untaken.length === 0) return;
  console.error(untaken[0]);
  if (typeof process !== "undefined") process.exitCode = 1;
}

// The program's code, when it waits or sends, as a task. The program ends
// after it, and what it started stops with it; a page goes on.
function main(code) {
  run(code, program, (ok, v) => {
    if (!ok) throw v;
    if (typeof process !== "undefined") process.exit();
  });
}

// A definition's task failed: the program ends here.
function finishNow() {
  finish();
  if (typeof process !== "undefined") process.exit();
  throw new Error("the program ended: its definition's task failed");
}

// -- Numbers --

// Halves away from zero, as vastra run rounds: (round -2.5) is -3.0.
function round(x) {
  return x < 0 ? -Math.round(-x) : Math.round(x);
}

function ceil(x) {
  return Math.ceil(x);
}

function truncate(x) {
  return Math.trunc(x);
}

// An Int's or a Float's distance from 0.
function abs(x) {
  return x < 0 ? -x : x === 0 ? 0 : x;
}

// bit/ on an Int, which has endless bits: as a BigInt, a number again when safe.
function bitAnd(a, b) {
  return whole(BigInt(a) & BigInt(b));
}

function bitOr(a, b) {
  return whole(BigInt(a) | BigInt(b));
}

function bitXor(a, b) {
  return whole(BigInt(a) ^ BigInt(b));
}

function bitNot(a) {
  return whole(~BigInt(a));
}

function bitShiftLeft(a, n) {
  const by = BigInt(n);
  return whole(by >= 0n ? BigInt(a) << by : BigInt(a) >> -by);
}

function bitShiftRight(a, n) {
  const by = BigInt(n);
  return whole(by >= 0n ? BigInt(a) >> by : BigInt(a) << -by);
}

// A fixed-width number shifted by n, within -32 to 32, its width's bits kept.
function shiftFixed(x, n, bits, signed, left) {
  const by = BigInt(Math.max(-32, Math.min(32, Number(n) * (left ? 1 : -1))));
  const v = by >= 0n ? BigInt(x) << by : BigInt(x) >> -by;
  return Number(signed ? BigInt.asIntN(bits, v) : BigInt.asUintN(bits, v));
}

// -- Strings: lengths and padding count Unicode characters --

function stringLength(s) {
  return [...s].length;
}

function stringSplit(s, separator) {
  return separator === "" ? [s] : s.split(separator);
}

// Lines without their \n or \r\n, and no empty one after a last \n.
function stringLines(s) {
  const lines = s.split("\n");
  if (lines[lines.length - 1] === "") lines.pop();
  return lines.map((l) => (l.endsWith("\r") ? l.slice(0, -1) : l));
}

// Without the spaces, tabs, newlines, returns and form feeds at its ends,
// the whitespace vastra run trims.
function stringTrim(s) {
  const space = " \t\n\r\f";
  let a = 0, b = s.length;
  while (a < b && space.includes(s[a])) a++;
  while (b > a && space.includes(s[b - 1])) b--;
  return s.slice(a, b);
}

function isStringBlank(s) {
  return stringTrim(s) === "";
}

function stringPadLeft(s, n) {
  return " ".repeat(Math.max(0, Number(n) - [...s].length)) + s;
}

function stringPadRight(s, n) {
  return s + " ".repeat(Math.max(0, Number(n) - [...s].length));
}

// -- Vectors --

function conj(xs, x) {
  return [...xs, x];
}

function cons(x, xs) {
  return [x, ...xs];
}

function nth(xs, i) {
  return i >= 0 && i < xs.length ? Some(xs[Number(i)]) : None;
}

// Combines in a tree that halves the vector, as every platform does, so it
// gives one result everywhere.
function parReduce(f, empty, xs) {
  const tree = (lo, hi) => {
    if (hi - lo === 1) return xs[lo];
    const mid = lo + Math.floor((hi - lo) / 2);
    return f(tree(lo, mid), tree(mid, hi));
  };
  return xs.length === 0 ? empty : tree(0, xs.length);
}

function take(n, xs) {
  return xs.slice(0, Math.max(0, Math.min(xs.length, Number(n))));
}

function drop(n, xs) {
  return xs.slice(Math.max(0, Math.min(xs.length, Number(n))));
}

function mapIndexed(f, xs) {
  return xs.map((x, i) => f(i, x));
}

function remove(f, xs) {
  return xs.filter((x) => !f(x));
}

function sort(xs) {
  return [...xs].sort(compare);
}

// Stable, by each element's key: before says which key comes first.
function sortBy(key, before, xs) {
  const keyed = xs.map((x) => [key(x), x]);
  keyed.sort((a, b) => (before(a[0], b[0]) ? -1 : before(b[0], a[0]) ? 1 : 0));
  return keyed.map((k) => k[1]);
}

function frequencies(xs) {
  let d = dictEmpty;
  for (const x of xs) {
    const seen = dictGet(x, d);
    d = dictInsert(x, seen.tag === "Some" ? seen[0] + 1 : 1, d);
  }
  return d;
}

function resultPartition(rs) {
  return { ok: rs.filter((r) => r.tag === "Ok").map((r) => r[0]), err: rs.filter((r) => r.tag === "Err").map((r) => r[0]) };
}

// -- The clock, in seconds --

function* clockNow() {
  return Date.now() / 1000;
}

// Since the program started, or the page loaded, from a clock that never jumps.
function* clockElapsed() {
  return performance.now() / 1000;
}

// Zero, less or NaN ends at once. A timer holds at most 2^31 - 1
// milliseconds, so a longer wait is several.
function* clockSleep(seconds) {
  for (let ms = seconds * 1000; ms > 0; ms -= 2147483647) {
    const part = Math.min(ms, 2147483647);
    yield new Wait((ended) => {
      const timer = setTimeout(ended, part, true);
      return () => clearTimeout(timer);
    });
  }
}

// -- Random numbers: the platform's randomness, for a seed --

function* randomSeed() {
  return { state: crypto.getRandomValues(new Uint32Array(1))[0] };
}

// -- Dictionaries --

// A Dict: its entries sorted by key, [[key, value], ...], never changed.
function Dict(entries) {
  this.entries = entries;
}

const dictEmpty = new Dict([]);

// The order of comparable values, as vastra run orders them: numbers, NaN
// below them all, and strings by code point.
function compare(a, b) {
  if (typeof a === "string") {
    let i = 0, j = 0;
    while (i < a.length && j < b.length) {
      const x = a.codePointAt(i), y = b.codePointAt(j);
      if (x !== y) return x < y ? -1 : 1;
      i += x > 65535 ? 2 : 1;
      j += y > 65535 ? 2 : 1;
    }
    return i < a.length ? 1 : j < b.length ? -1 : 0;
  }
  if (a !== a || b !== b) return a !== a ? (b !== b ? 0 : -1) : 1;
  return a < b ? -1 : a > b ? 1 : 0;
}

// Where key is in sorted entries, or where it would go: [index, found].
function place(entries, key) {
  let lo = 0, hi = entries.length;
  while (lo < hi) {
    const mid = (lo + hi) >> 1, c = compare(entries[mid][0], key);
    if (c === 0) return [mid, true];
    if (c < 0) lo = mid + 1;
    else hi = mid;
  }
  return [lo, false];
}

function dictInsert(key, value, d) {
  const [i, found] = place(d.entries, key), entries = d.entries.slice();
  entries.splice(i, found ? 1 : 0, [key, value]);
  return new Dict(entries);
}

// What is at path in v, as an Option: a step may be missing, an index, a
// dictionary's key, or a key that may be missing.
function getPath(v, path) {
  for (const step of path) {
    if (v instanceof Dict) {
      const [i, found] = place(v.entries, step);
      if (!found) return None;
      v = v.entries[i][1];
    } else if (typeof step === "string") {
      if (!Object.hasOwn(v, step)) return None;
      v = v[step];
    } else {
      if (!(step >= 0 && step < v.length)) return None;
      v = v[Number(step)];
    }
  }
  return Some(v);
}

// v with what is at path replaced by f(old), or by f() when adds (a set) and
// the last step is missing. A missing index, dictionary key or key that may
// be missing leaves v as it is. A buffer changes in place: no one else holds it.
function change(v, path, f, adds, from = 0) {
  if (from === path.length) return f(v);
  const step = path[from], deeper = (old) => change(old, path, f, adds, from + 1);
  const adding = adds && from === path.length - 1;
  if (v instanceof Dict) {
    const [i, found] = place(v.entries, step);
    return found ? dictInsert(step, deeper(v.entries[i][1]), v) : adding ? dictInsert(step, f(), v) : v;
  }
  if (typeof step === "string") {
    return Object.hasOwn(v, step) ? { ...v, [step]: deeper(v[step]) } : adding ? { ...v, [step]: f() } : v;
  }
  const copy = () => (Array.isArray(v) ? v.slice() : v);
  if (step >= 0 && step < v.length) return put(copy(), Number(step), deeper(v[Number(step)]));
  return adding && step == v.length ? put(copy(), v.length, f()) : v;
}

function dictGet(key, d) {
  const [i, found] = place(d.entries, key);
  return found ? Some(d.entries[i][1]) : None;
}

function dictCount(d) {
  return d.entries.length;
}

function dictEntries(d) {
  return d.entries.map((e) => ({ key: e[0], value: e[1] }));
}

// -- JSON --

// A JavaScript value as Json: what isn't data is JNull.
function json(v) {
  if (typeof v === "boolean") return { tag: "JBool", 0: v };
  if (typeof v === "number") return { tag: "JNumber", 0: v };
  if (typeof v === "string") return { tag: "JString", 0: v };
  if (v === null || typeof v !== "object") return { tag: "JNull" };
  if (Array.isArray(v)) return { tag: "JArray", 0: v.map(json) };
  let d = dictEmpty;
  for (const k of Object.keys(v)) d = dictInsert(k, json(v[k]), d);
  return { tag: "JObject", 0: d };
}

// JSON text as JavaScript values, or why not, in vastra run's words: where
// is a character count in UTF-8, as vastra run counts.
function parseJson(text) {
  let pos = 0;
  const peek = () => text[pos];
  const fail = (what) => {
    throw what + " at character " + (new TextEncoder().encode(text.slice(0, pos)).length + 1);
  };
  const blank = () => {
    while (peek() === " " || peek() === "\n" || peek() === "\r" || peek() === "\t") pos++;
  };
  const expect = (s) => {
    if (!text.startsWith(s, pos)) fail("expected " + s);
    pos += s.length;
  };
  const hex4 = () => {
    const digits = text.slice(pos, pos + 4);
    if (digits.length < 4 || ![...digits].every((c) => "0123456789abcdefABCDEF".includes(c))) fail("invalid \\u escape");
    pos += 4;
    return parseInt(digits, 16);
  };
  const string = () => {
    expect("\"");
    let out = "";
    for (;;) {
      const c = peek();
      if (c === undefined) fail("unterminated string");
      pos++;
      if (c === "\"") return out;
      if (c !== "\\") {
        out += c;
        continue;
      }
      const e = peek();
      pos++;
      if (e === "\"" || e === "\\" || e === "/") out += e;
      else if (e === "n") out += "\n";
      else if (e === "t") out += "\t";
      else if (e === "r") out += "\r";
      else if (e === "b") out += "\b";
      else if (e === "f") out += "\f";
      else if (e === "u") {
        const start = pos;
        let code = hex4();
        if (code >= 55296 && code < 56320 && text.startsWith("\\u", pos)) {
          pos += 2;
          const low = hex4();
          if (low >= 56320 && low < 57344) code = 65536 + ((code - 55296) << 10) + (low - 56320);
        }
        if (code >= 55296 && code < 57344) {
          pos = start;
          fail("invalid \\u escape");
        }
        out += String.fromCodePoint(code);
      } else fail("invalid escape");
    }
  };
  const value = () => {
    blank();
    const c = peek();
    if (c === "{") {
      pos++;
      blank();
      const out = Object.create(null);
      if (peek() === "}") {
        pos++;
        return out;
      }
      for (;;) {
        blank();
        const k = string();
        blank();
        expect(":");
        out[k] = value();
        blank();
        if (peek() !== ",") break;
        pos++;
      }
      expect("}");
      return out;
    }
    if (c === "[") {
      pos++;
      blank();
      const out = [];
      if (peek() === "]") {
        pos++;
        return out;
      }
      for (;;) {
        out.push(value());
        blank();
        if (peek() !== ",") break;
        pos++;
      }
      expect("]");
      return out;
    }
    if (c === "\"") return string();
    for (const [word, v] of [["true", true], ["false", false], ["null", null]]) {
      if (text.startsWith(word, pos)) {
        pos += word.length;
        return v;
      }
    }
    if (c !== undefined && "-0123456789".includes(c)) {
      const start = pos;
      while (peek() !== undefined && "-+.eE0123456789".includes(peek())) pos++;
      const n = Number(text.slice(start, pos));
      if (n !== n) fail("invalid number");
      return n;
    }
    fail("expected a JSON value");
  };
  const v = value();
  blank();
  if (pos !== text.length) fail("unexpected text after the JSON value");
  return v;
}

function jsonParse(text) {
  try {
    return { tag: "Ok", 0: json(parseJson(text)) };
  } catch (why) {
    if (typeof why !== "string") throw why;
    return { tag: "Err", 0: why };
  }
}

// -- HTTP --

// A GET, as an Answer: {status, headers, body}, header names lowercase, a
// repeated one's values joined with ", ". One outside 200-299 is BadStatus.
function* request(url) {
  let response, body;
  try {
    response = yield fetch(url);
    body = yield response.text();
  } catch (_) {
    const page = typeof document !== "undefined" || URL.canParse(url);
    throw new Failure({ tag: "NetworkError", 0: "cannot reach " + url + (page ? "" : ": outside a page, a URL starts with http://") });
  }
  let headers = dictEmpty;
  response.headers.forEach((value, name) => (headers = dictInsert(name, value, headers)));
  const answer = { status: response.status, headers: headers, body: body };
  if (response.status >= 200 && response.status < 300) return answer;
  throw new Failure({ tag: "BadStatus", 0: response.status, 1: answer });
}

function* httpGetText(url) {
  return (yield request(url)).body;
}

// Told a written type, the body is decoded to it: a body that isn't JSON, and
// JSON of the wrong shape, are both BadBody.
function* httpGet(shape, url) {
  const answer = yield request(url);
  if (shape === null) return answer;
  const bad = (why) => {
    if (typeof why !== "string") throw why;
    throw new Failure({ tag: "BadBody", 0: why });
  };
  let parsed;
  try {
    parsed = parseJson(answer.body);
  } catch (why) {
    bad(typeof why === "string" ? "not JSON: " + why : why);
  }
  try {
    return decode(shape, parsed, "");
  } catch (why) {
    bad(why);
  }
}

// -- Files: Node's; a page has none --

function files() {
  if (typeof process === "undefined") throw new Error("a page has no files");
  return process.getBuiltinModule("node:fs");
}

// The error kinds, whatever the platform's wording.
function fileError(x) {
  if (x.code === "ENOENT") return { tag: "NotFound" };
  if (x.code === "EACCES") return { tag: "PermissionDenied" };
  return { tag: "Other", 0: x.message };
}

function* fileReadText(path) {
  let bytes;
  try {
    bytes = files().readFileSync(path);
  } catch (x) {
    throw new Failure(fileError(x));
  }
  try {
    return new TextDecoder("utf-8", { fatal: true, ignoreBOM: true }).decode(bytes);
  } catch (_) {
    throw new Failure({ tag: "Other", 0: "the file is not valid UTF-8 text" });
  }
}

function* fileWriteText(path, text) {
  try {
    files().writeFileSync(path, text);
  } catch (x) {
    throw new Failure(fileError(x));
  }
}

// -- Strings, the console, the command line --

function stringJoin(separator, xs) {
  return Array.from(xs).join(separator);
}

function* consolePrintError(text) {
  console.error(text);
}

// Ends the program with this status; in a page, it sets the status only.
function* cliExit(code) {
  if (typeof process !== "undefined") process.exit(Number(code));
}

// -- JavaScript reached from the program: vastra.js --

// A key that may be missing, read as an Option.
function maybe(x) {
  return x === undefined ? None : Some(x);
}

// What a JavaScript value is, in an error: a string itself, or "a number".
function found(v) {
  if (typeof v === "string") return quote(v);
  if (v == null) return "null";
  if (typeof v === "boolean") return "a boolean";
  if (typeof v === "number") return "a number";
  return Array.isArray(v) ? "an array" : "an object";
}

function alternatives(words) {
  return words.length < 2 ? words.join("") : words.slice(0, -1).join(", ") + " or " + words[words.length - 1];
}

// [v], from JavaScript or JSON, as a value of the written type [shape], read
// only where the shape looks. A misfit throws why, saying where, as vastra run
// says it: in [1].gender: expected a string, found a number.
function decode(shape, v, path) {
  const fail = (what) => {
    const where = path.startsWith(".") ? path.slice(1) : path;
    throw where === "" ? what : "in " + where + ": " + what;
  };
  const expected = (what) => fail("expected " + what + ", found " + found(v));
  if (shape === "Json") return json(v);
  if (shape === "Int") return Number.isInteger(v) ? (Number.isSafeInteger(v) ? v : BigInt(v)) : expected("a whole number");
  if (shape === "Float") return typeof v === "number" ? v : expected("a number");
  if (shape === "String") return typeof v === "string" ? v : expected("a string");
  if (shape === "Bool") return typeof v === "boolean" ? v : expected("a boolean");
  if (shape.option) return v == null ? None : Some(decode(shape.option, v, path));
  if (shape.vector) return Array.isArray(v) ? v.map((x, i) => decode(shape.vector, x, path + "[" + i + "]")) : expected("an array");
  if (shape.record) {
    if (typeof v !== "object" || v === null || Array.isArray(v)) return expected("an object");
    const out = {};
    for (const [k, s] of shape.record) {
      const optional = k.endsWith("?"), name = optional ? k.slice(0, -1) : k, x = v[name];
      if (x !== undefined) out[k] = decode(s, x, path + "." + name);
      else if (!optional) fail("missing field \"" + name + "\"");
    }
    return out;
  }
  const word = shape.words.find((w) => w[0] === v);
  return word ? word[1] : expected(alternatives(shape.words.map((w) => quote(w[0]))));
}

// A Json value, from json/parse, as the JavaScript value it stands for.
function plain(j) {
  switch (j.tag) {
    case "JNull": return null;
    case "JBool": case "JNumber": case "JString": return j[0];
    case "JArray": return j[0].map(plain);
    case "JObject": {
      const out = Object.create(null);
      for (const [k, v] of j[0].entries) out[k] = plain(v);
      return out;
    }
  }
  return j;
}

// The same as a Result: (Ok value), or (Err why). Given a Json value or a
// JavaScript one.
function decoded(shape, v) {
  const given = v !== null && typeof v === "object" && typeof v.tag === "string" && v.tag[0] === "J" ? plain(v) : v;
  try {
    return { tag: "Ok", 0: decode(shape, given, "") };
  } catch (why) {
    if (typeof why !== "string") throw why;
    return { tag: "Err", 0: why };
  }
}

// A value that can't go to JavaScript, and why: the call given it fails.
function Refused(why) {
  this.why = why;
}

// A value going to JavaScript, by the rules for JSON: maps become objects,
// vectors arrays, a constructor its outside word, None null. An object with
// a tag is taken for a constructor.
function encode(v) {
  try {
    return encoded(v);
  } catch (x) {
    if (x instanceof Refused) return x;
    throw x;
  }
}

function encoded(v) {
  if (typeof v === "bigint") return Number(v);
  if (v === null || typeof v !== "object") {
    if (typeof v === "function") throw new Refused("a function: give it with js/callback");
    return v;
  }
  if (v instanceof Refused) throw v;
  if (Array.isArray(v) || ArrayBuffer.isView(v)) return Array.from(v, encoded);
  if (v instanceof Dict) {
    const out = {};
    for (const [k, x] of v.entries) {
      if (typeof k !== "string") throw new Refused("a Dict not keyed by text");
      out[k] = encoded(x);
    }
    return out;
  }
  if (typeof v.tag === "string") {
    if (v.tag === "None") return null;
    if (v.tag === "Some") return encoded(v[0]);
    if (0 in v) throw new Refused(v.tag + ", which holds values");
    if (v.word === undefined) throw new Refused(v.tag + ", which has no outside word");
    return v.word;
  }
  const out = {};
  for (const k of Object.keys(v)) out[k.endsWith("?") ? k.slice(0, -1) : k] = encoded(v[k]);
  return out;
}

// An exception, or what a Promise was rejected with: (Thrown name message).
function thrown(r) {
  const parts = r instanceof Error ? [r.name, r.message] : ["Error", String(r)];
  return new Failure({ tag: "Thrown", 0: parts[0], 1: parts[1] });
}

// What a JavaScript call gives, waited for if a Promise, as the type its let
// was told; with none, as it is.
function* answer(shape, act) {
  let v;
  try {
    v = act();
    if (v != null && typeof v.then === "function") v = yield v;
  } catch (r) {
    throw r instanceof Failure ? r : thrown(r);
  }
  if (shape === null) return v;
  try {
    return decode(shape, v, "");
  } catch (why) {
    if (typeof why !== "string") throw why;
    throw new Failure({ tag: "BadValue", 0: why });
  }
}

function present(owner, what, key) {
  if (owner != null && key in Object(owner)) return owner[key];
  throw new Failure({ tag: "Missing", 0: what + " " + key });
}

function given(xs) {
  for (const x of xs) if (x instanceof Refused) throw new Failure({ tag: "BadArgument", 0: x.why });
  return xs;
}

function* jsGlobal(shape, name) {
  return yield answer(shape, () => present(globalThis, "global", name));
}

function* jsGet(shape, owner, key) {
  return yield answer(shape, () => present(owner, "property", key));
}

function* jsCall_(shape, f, xs) {
  return yield answer(shape, () => f(...given(xs)));
}

function* jsMethod_(shape, owner, name, xs) {
  return yield answer(shape, () => present(owner, "method", name).apply(owner, given(xs)));
}

function* jsNew_(shape, make, xs) {
  return yield answer(shape, () => new make(...given(xs)));
}

function* jsSet(owner, key, v) {
  yield answer(null, () => {
    owner[key] = given([v])[0];
  });
}

// A function JavaScript can call with its first n arguments. It runs as a
// handler does: a task it gives runs, then what was sent, and the views draw
// again. What it gives goes back to JavaScript, as js/value gives it.
function jsCallback_(n, f) {
  return (...args) => {
    const r = f(...Array.from({ length: n }, (_, i) => args[i]));
    const task = typeof r === "function" || String(r) === "[object Generator]";
    if (task) run(r, program, handled);
    handleSent();
    redraw();
    const back = task || r === undefined ? undefined : encode(r);
    return back instanceof Refused ? undefined : back;
  };
}

// The program's arguments, as a task.
function* cliArgs() {
  return process.argv.slice(2);
}

// quot and mod: dividing by zero gives None.
function quot(a, b) {
  return b == 0 ? None : Some(quotient(a, b));
}

function mod(a, b) {
  return b == 0 ? None : Some(remainder(a, b));
}
