// Checks Vastra in a real browser (headless Chrome), on the test pages in
// fixtures/: a counter, a fetch-and-decode page, answers decoded by the type
// written on their let (in a page and in Node), requests that wait together,
// stopping a request, a timer, html, pointer events, a page's state changed
// from the prompt and recorded, a page's REPL into itself, the REPL and
// `vastra serve`.
//
//   dune build @browser
//   (or: node web/test/check.mjs PATH/TO/vastra PATH/TO/compiled-counter.js)

import { execFile, spawn } from "node:child_process";
import fs from "node:fs";
import http from "node:http";
import net from "node:net";
import os from "node:os";
import path from "node:path";
import { promisify } from "node:util";

const vastra = path.resolve(process.argv[2]);
const counterJs = path.resolve(process.argv[3]);
const root = path.resolve(path.dirname(new URL(import.meta.url).pathname), "../..");
const sleep = (ms) => new Promise((resolve) => setTimeout(resolve, ms));

// The pages, in one folder served by `vastra serve`: /fixtures/ the test pages,
// / the REPL. No folder has a vastra.js: the command gives it.
const site = fs.mkdtempSync(path.join(os.tmpdir(), "vastra-site-"));
const copy = (from, to) => fs.cpSync(path.join(root, from), path.join(site, to),
  { recursive: true, filter: (file) => path.basename(file) !== "vastra.js" });
copy("web/test/fixtures", "fixtures");
copy("web/repl.html", "index.html");
fs.copyFileSync(counterJs, path.join(site, "fixtures/compiled/counter.js"));
// Copies of dune's files are read-only; the checks edit them.
for (const file of fs.readdirSync(site, { recursive: true })) fs.chmodSync(path.join(site, file), 0o755);
const outside = `${site}.txt`;
fs.writeFileSync(outside, "not served");

const port = await new Promise((resolve) => {
  const probe = net.createServer().listen(0, "127.0.0.1", () => {
    const { port } = probe.address();
    probe.close(() => resolve(port));
  });
});
const serve = spawn(vastra, ["serve", "--port", String(port), site]);
process.on("exit", () => serve.kill());
let terminal = "";
serve.stdout.on("data", (d) => { terminal += d; });
serve.stderr.on("data", (d) => { terminal += d; });
const until = async (condition) => {
  for (let i = 0; i < 50; i++) { if (await condition()) return true; await sleep(100); }
  return false;
};
const heard = (line, since) => until(async () => terminal.indexOf(line, since) >= 0);
// A line typed into serve's terminal, a REPL into the page; gives where its answer starts.
const ask = (line) => {
  const since = terminal.length;
  serve.stdin.write(line + "\n");
  return since;
};
await heard("Serving", 0);
const base = `http://127.0.0.1:${port}`;
const beforeAnyPage = ask("(+ 1 2)");
const waits = await heard(`waiting for a page: open http://localhost:${port}`,
  beforeAnyPage);
// The status of a path sent as written (fetch would resolve "..").
const status = (pathname) => new Promise((resolve) =>
  http.get({ host: "127.0.0.1", port, path: pathname }, (res) => { res.resume(); resolve(res.statusCode); }));

const profile = fs.mkdtempSync(path.join(os.tmpdir(), "vastra-chrome-"));
const chrome = spawn("google-chrome", ["--headless=new", "--disable-gpu", "--no-first-run",
  `--user-data-dir=${profile}`, "--remote-debugging-port=0", "about:blank"],
  { stdio: ["ignore", "ignore", "pipe"], detached: true });
const wsUrl = await new Promise((resolve) => chrome.stderr.on("data", (d) => {
  const m = /ws:\/\/\S+/.exec(d.toString());
  if (m) resolve(m[0]);
}));

// The DevTools protocol, one page.
const ws = new WebSocket(wsUrl);
await new Promise((resolve) => ws.addEventListener("open", resolve));
let next = 0;
const waiting = new Map();
ws.addEventListener("message", (event) => {
  const message = JSON.parse(event.data);
  if (waiting.has(message.id)) { waiting.get(message.id)(message); waiting.delete(message.id); }
});
const send = (method, params = {}, sessionId) => new Promise((resolve) => {
  const id = ++next;
  waiting.set(id, resolve);
  ws.send(JSON.stringify({ id, method, params, sessionId }));
});
const { result: { targetId } } = await send("Target.createTarget", { url: "about:blank" });
const { result: { sessionId } } = await send("Target.attachToTarget", { targetId, flatten: true });
const page = (method, params) => send(method, params, sessionId);

const evaluate = async (expression, session = sessionId) => {
  const reply = await send("Runtime.evaluate", { expression, returnByValue: true, awaitPromise: true }, session);
  return reply.result.result.value;
};
const open = async (url) => {
  await page("Page.navigate", { url: base + url });
  for (let i = 0; i < 50; i++) {
    await sleep(100);
    if (await evaluate("document.readyState === 'complete' && document.body.children.length > 0")) break;
  }
  await sleep(300);
};
const text = (selector) => evaluate(`document.querySelector(${JSON.stringify(selector)})?.textContent ?? null`);
const button = (label) => `[...document.querySelectorAll("button")].find((b) => b.textContent === ${JSON.stringify(label)})`;
const click = async (label) => { await evaluate(`${button(label)}.click()`); await sleep(50); };
const disabled = (label) => evaluate(`${button(label)}.disabled`);
const type = async (value) => {
  await evaluate(`(() => { const i = document.querySelector("input"); i.value = ${JSON.stringify(value)};
    i.dispatchEvent(new Event("input")); })()`);
  await sleep(50);
};

let failures = 0;
const check = (what, actual, expected) => {
  const ok = JSON.stringify(actual) === JSON.stringify(expected);
  if (!ok) failures++;
  console.log(`${ok ? "  ok  " : "  FAIL"} ${what}${ok ? "" : `: expected ${JSON.stringify(expected)}, got ${JSON.stringify(actual)}`}`);
};

// What the counter does: its state, messages, invalid input and storage.
const counter = async (title, url) => {
  console.log(title);
  await evaluate("localStorage.clear()").catch(() => {});
  await open(url);
  await evaluate("localStorage.clear()");
  await open(url);
  check("opens at 0", await text(".count"), "0");
  check("shows the title", await text("h1"), "Counter");
  for (let i = 0; i < 3; i++) await click("+");
  check("+ three times gives 3", await text(".count"), "3");
  await type("5");
  await click("+");
  check("step 5, then + gives 8", await text(".count"), "8");
  await click("−");
  check("− gives 3", await text(".count"), "3");
  await type("five");
  check("an invalid step explains itself", await text(".error"), "The step must be a whole number.");
  check("+ is disabled", await disabled("+"), true);
  check("− is disabled", await disabled("−"), true);
  check("Reset still works", await disabled("Reset"), false);
  await type("0");
  check("a zero step explains itself", await text(".error"), "The step must be greater than zero.");
  await type("1");
  check("a valid step removes the message", await text(".error"), null);
  await open(url);
  check("after a reload the count is still there", await text(".count"), "3");
  await click("Reset");
  check("Reset gives 0", await text(".count"), "0");
};

// The first page to connect runs what the REPL was given before.
await open("/fixtures/counter/index.html");
const ranInFirstPage = await heard("3 : Int", beforeAnyPage);

await counter("counter, interpreted by vastra.js:", "/fixtures/counter/index.html");
await counter("counter compiled with vastra build --js:", "/fixtures/compiled/index.html");

console.log("counter with storage blocked:");
await open("/fixtures/blocked/index.html");
check("opens at 0", await text(".count"), "0");
await click("+");
check("+ still works", await text(".count"), "1");
check("no error is shown", await text(".vastra-error"), null);

console.log("a program with a type error:");
await open("/fixtures/broken/index.html");
const error = await text(".vastra-error");
check("the page shows the error", error?.split("\n")[0],
  "type error: `double` takes a number, and this is a String");

console.log("a page requiring a module for native code:");
await open("/fixtures/window/index.html");
check("the page refuses it", (await text(".vastra-error"))?.split("\n")[0],
  "name error: the module vastra.window runs only on native, not on js");

console.log("fetching and decoding JSON:");
await open("/fixtures/fetch/index.html");
await sleep(500);
check("each request gives a typed result", await evaluate(`[...document.querySelectorAll("li")].map((li) => li.textContent)`), [
  "Ana is 30",
  "failed: the server answered 404: File not found",
  'failed: in field "age": expected a whole number, found a string',
]);

console.log("answers told their type by the let:");
await open("/fixtures/answers/index.html");
const told = () => evaluate(`[...document.querySelectorAll("li")].map((li) => li.textContent)`);
await until(async () => (await told()).length === 5);
check("a request decodes its body, or fails in one of three ways", await told(), [
  "Madam Ada, Madam Grace, Sir Edsger",
  'unexpected answer: in [1].gender: expected "female" or "male", found "f"',
  "unexpected answer: not JSON: expected a JSON value at character 1",
  "the server answered 404: File not found",
  "200 no-store hello",
]);
const unanswered = terminal.length;
await open("/fixtures/answers/wrong.html");
const answerType = "{:status Int, :headers (Dict String String), :body String}";
check("with no type written, the answer is an Answer",
  await heard(`type error: expected ${answerType}, found number`, unanswered), true);
check("the error stays out of the page", await text(".vastra-error"), null);
check("whose file never checked, so it got an empty program",
  await (await fetch(base + "/fixtures/answers/wrong.vas")).text(), "");

// The same requests from a program built for Node, which has no XMLHttpRequest,
// and one to a server that gives a header twice.
console.log("requests from a program built for Node:");
const twice = http.createServer((req, res) => { res.setHeader("X-Twice", ["one", "two"]); res.end("twice"); });
await new Promise((resolve) => twice.listen(0, "127.0.0.1", resolve));
const nodeJs = path.join(site, "node.js");
const run = promisify(execFile);
await run(vastra, ["build", "--js", path.join(site, "fixtures/answers/node.vas"), "-o", nodeJs]);
const ran = await run("node", [nodeJs, `${base}/fixtures/answers/`, `http://127.0.0.1:${twice.address().port}/`]);
twice.close();
check("they give what the page's do, and fail the same ways", ran.stdout.split("\n"), [
  "Ada, Grace, Edsger",
  'unexpected answer: in [1].gender: expected "female" or "male", found "f"',
  "unexpected answer: not JSON: expected a JSON value at character 1",
  "the server answered 404: File not found",
  "200 no-store hello",
  "200 one, two twice",
  "network error: cannot reach http://127.0.0.1:1/users.json",
  "network error: cannot reach users.json: outside a page, a URL starts with http://",
  "",
]);

console.log("JavaScript from a program built for Node:");
const jsNode = path.join(site, "fixtures/js/node.js");
await run(vastra, ["build", "--js", path.join(site, "fixtures/js/node.vas"), "-o", jsNode]);
check("it imports ES modules; calls are decoded by their let's type, and fail their ways",
  (await run("node", [jsNode])).stdout.split("\n"), [
  "hello, node, area 12",
  "max 9",
  '{"name":"Ada","age":36,"title":"Dr","mood":"busy","pet":null}',
  'Ada (Some "Dr")',
  "year 1970",
  "note set",
  "waited for 42",
  "doubled [2 4 6]",
  "sorted [1 2 3], total 6",
  'misfits ["a" "expected a string, found a number"]',
  'passed as they are ["a",2]',
  "read loop and k",
  "no global Nowhere",
  "no method maxx",
  "no property size",
  "SyntaxError: Expected property name or '}' in JSON at position 1 (line 1 column 2)",
  "Error: no",
  "can't give JavaScript a function: give it with js/callback",
  "can't give JavaScript Ok, which holds values",
  'unexpected value: expected a whole number, found "1"',
  "",
]);

// Chrome holds each answer until every request has been answered, then lets
// them through last first, one at a time.
console.log("requests that wait together:");
const answers = new Map();
const holdAnswer = (event) => {
  const { method, params } = JSON.parse(event.data);
  if (method === "Fetch.requestPaused") answers.set(path.basename(params.request.url), params.requestId);
};
ws.addEventListener("message", holdAnswer);
await page("Fetch.enable", { patterns: [{ urlPattern: "*/fixtures/concurrent/*.txt", requestStage: "Response" }] });
await open("/fixtures/concurrent/index.html");
check("every request is sent before the first answer is handled", await until(async () => answers.size === 3), true);
const items = (list) => evaluate(`JSON.stringify([...document.querySelectorAll(".${list} li")].map((li) => li.textContent))`);
for (const [file, waiting] of [["three.txt", ["one.txt", "missing.txt"]], ["missing.txt", ["one.txt"]], ["one.txt", []]]) {
  await page("Fetch.continueRequest", { requestId: answers.get(file) });
  check(`the answer for ${file} changes the state when it comes`,
    await until(async () => (await items("waiting")) === JSON.stringify(waiting)), true);
}
check("one result per URL, in the URLs' order", JSON.parse(await items("results")),
  ["one", "the server answered 404: File not found", "three"]);
await page("Fetch.disable");
ws.removeEventListener("message", holdAnswer);

// A search: Chrome holds each answer, so a request is still waiting when
// the next letter, or clear, stops it.
console.log("stopping a request that waits:");
const searches = [];
const holdSearch = (event) => {
  const { method, params } = JSON.parse(event.data);
  if (method === "Fetch.requestPaused") searches.push(params.requestId);
};
ws.addEventListener("message", holdSearch);
await page("Fetch.enable", { patterns: [{ urlPattern: "*/fixtures/search/answer.txt*", requestStage: "Response" }] });
await open("/fixtures/search/index.html");
await type("v");
await type("va");
check("each letter sends a request", await until(async () => searches.length === 2), true);
check("and it is loading", await text(".loading"), "true");
await page("Fetch.continueRequest", { requestId: searches[1] });
check("the answer it wants arrives",
  await until(async () => (await text(".results")) === "va: the answer"), true);
await page("Fetch.continueRequest", { requestId: searches[0] });
await type("vas");
check("another letter, another request", await until(async () => searches.length === 3), true);
await click("clear");
await page("Fetch.continueRequest", { requestId: searches[2] });
await sleep(300);
check("a stopped request's answer never reaches its clauses, and clear resets",
  [await text(".results"), await text(".loading"), await text(".answers")], ["", "false", "1"]);
await page("Fetch.disable");
ws.removeEventListener("message", holdSearch);

console.log("a repeating timer, and stopping it:");
await open("/fixtures/stopwatch/index.html");
await click("start");
check("it ticks, each tick after a sleep", await until(async () => Number(await text(".ticks")) >= 3), true);
await click("pause");
const paused = await text(".ticks");
await sleep(400);
check("pause stops it: no tick comes after", await text(".ticks"), paused);
const tickedAt = Number(await text(".shown"));
check("a tick carries clock/elapsed, the seconds since the page loaded",
  tickedAt > 0 && tickedAt < (await evaluate("performance.now()")) / 1000, true);

console.log("html:");
await open("/fixtures/board/index.html");
const cells = `document.querySelectorAll(".board > button.cell")`;
check("a for inside a for puts its elements in place", await evaluate(`${cells}.length`), 9);
check("a string key is an attribute named as written",
  await evaluate(`document.querySelector(".board").dataset.size`), "3");
check("text computed in an if", await text(`[data-at="1,0"]`), "first");
await evaluate(`document.querySelector('[data-at="1,2"]').click()`);
await sleep(50);
check("an element made in a for handles its message", await text(".moves"), "Moves: 1");
check("a custom element, its children given by map", await text("move-log"), "1,2");

// Real mouse input, through Chrome; each step waits two frames, since moves
// reach update once per frame.
console.log("pointer events:");
await open("/fixtures/pointer/index.html");
const frame = () => evaluate("new Promise((r) => requestAnimationFrame(() => requestAnimationFrame(r)))");
const mouse = async (type, x, y, button, buttons) => {
  await page("Input.dispatchMouseEvent", { type, x, y, button, buttons, clickCount: 1 });
  await frame();
};
const pointerLog = () => text("#box");
const aftersBefore = await evaluate("window.afters");
await mouse("mouseMoved", 50, 50, "none", 0);
await mouse("mouseMoved", 60, 60, "none", 0);
check("moves over the box unpressed change nothing: nothing prints",
  await evaluate("window.afters"), aftersBefore);
await mouse("mousePressed", 20, 30, "left", 1);
check("a press says where", await pointerLog(), "ready, down 20.0 30.0");
check("and when, in seconds on the clock of clock/now",
  Math.abs(Number(await text("#time")) - Date.now() / 1000) < 5, true);
check("a press reaches its handler, which prints", (await evaluate("window.afters")) > aftersBefore, true);
await mouse("mouseMoved", 400, 300, "left", 1);
check("the pressed box keeps the pointer: a move outside it reaches it",
  await pointerLog(), "ready, down 20.0 30.0, move 400.0 300.0");
await mouse("mouseReleased", 410, 310, "left", 0);
check("so does the release", await pointerLog(), "ready, down 20.0 30.0, move 400.0 300.0, up 410.0 310.0");
await mouse("mousePressed", 20, 20, "right", 2);
await mouse("mouseReleased", 20, 20, "right", 0);
check("other buttons belong to the browser",
  await pointerLog(), "ready, down 20.0 30.0, move 400.0 300.0, up 410.0 310.0");
await mouse("mousePressed", 10, 10, "left", 1);
await evaluate(`(() => { const box = document.querySelector("#box");
  for (const x of [11, 12, 13]) box.dispatchEvent(new PointerEvent("pointermove", { clientX: x, clientY: 10 })); })()`);
await frame();
check("moves within one frame reach the handlers once, the latest",
  (await pointerLog()).endsWith("down 10.0 10.0, move 13.0 10.0"), true);
await evaluate(`document.querySelector("#box").dispatchEvent(new PointerEvent("pointercancel"))`);
await frame();
check("a pointer the browser takes over is released where it was last seen",
  (await pointerLog()).endsWith("move 13.0 10.0, up 13.0 10.0"), true);
await mouse("mouseReleased", 13, 10, "left", 0);

console.log("the REPL (web/repl.html):");
await open("/");
check("opens at the folder's own address", await evaluate("location.pathname"), "/");
check("defines", await evaluate(`vastra.eval("(fn square [x] (* x x))")`), "square : (-> number number)");
check("evaluates", await evaluate(`vastra.eval("(square 7)")`), "49 : Int");
check("keeps definitions after an error", (await evaluate(`vastra.eval("(square \\"a\\")")`)).split("\n")[0],
  "type error: `square` takes a number, and this is a String");
check("and after it", await evaluate(`vastra.eval("(square 8)")`), "64 : Int");

console.log("vastra serve:");
check("the counter's folder has no vastra.js", fs.existsSync(path.join(site, "fixtures/counter/vastra.js")), false);
check("a missing file is not found", await status("/fixtures/counter/missing.vas"), 404);
check("a path outside the folder is refused", await status(`/../${path.basename(outside)}`), 403);
check("also written %2e%2e", await status(`/%2e%2e/${path.basename(outside)}`), 403);
const folder = (pathname) => fetch(base + pathname, { redirect: "manual" })
  .then((res) => [res.status, res.headers.get("location")]);
check("a folder's address gives its index.html in place", await folder("/"), [200, null]);
check("an .svg is served as an image",
  await fetch(base + "/fixtures/dot.svg").then((r) => r.headers.get("content-type")), "image/svg+xml");
check("without its last /, it is sent there", await folder("/fixtures/counter"),
  [301, "/fixtures/counter/"]);
check("a REPL line before any page connects waits for one", waits, true);
check("the first page to connect runs it", ranInFirstPage, true);
const unloaded = path.join(site, "fixtures/no-vastra-js/index.html");
const lacks = "fixtures/no-vastra-js/index.html has a text/vastra script but no vastra.js: " +
  'add <script src="vastra.js" defer></script>';
const named = (line) => terminal.split(line).length - 1;
await open("/fixtures/no-vastra-js/index.html");
check("a page with a text/vastra script but no vastra.js is named", await heard(lacks, 0), true);
await open("/fixtures/no-vastra-js/index.html");
check("only that page, once until it's saved", named("but no vastra.js"), 1);
fs.appendFileSync(unloaded, "\n<!-- saved -->\n");
await open("/fixtures/no-vastra-js/index.html");
check("and again after a save", named(lacks), 2);
const firstEvent = (pathname) => new Promise((resolve) => {
  const request = http.get({ host: "127.0.0.1", port, path: pathname }, (res) => {
    let data = "";
    res.on("data", (d) => { data += d; if (data.includes("\n\n")) { request.destroy(); resolve(data); } });
  });
});
check("a page running another vastra.js is told to reload",
  (await firstEvent("/.vastra/live?build=older")).includes("data: reload"), true);

// Editing the counter while it runs: a save restarts the lines that
// changed, and the other names keep their values.
console.log("vastra serve, editing the counter while it runs:");
const counterVas = path.join(site, "fixtures/counter/counter.vas");
// Each pair of arguments is a text and what replaces it, in one save.
const rewrite = (file, ...pairs) => {
  const since = terminal.length;
  let text = fs.readFileSync(file, "utf8");
  for (let i = 0; i < pairs.length; i += 2) text = text.replace(pairs[i], pairs[i + 1]);
  fs.writeFileSync(file, text);
  return since;
};
const edit = (...pairs) => rewrite(counterVas, ...pairs);
const state = async () => [await text(".count"), await evaluate(`document.querySelector("input").value`)];
await evaluate("localStorage.clear()");
await open("/fixtures/counter/index.html");
await type("5");
await click("+");
await click("+");
check("the state before editing", await state(), ["10", "5"]);
let since = edit('[:h1 "Counter"]', '[:h1 "Live counter"]');
check("a changed text shows", await until(async () => (await text("h1")) === "Live counter"), true);
check("the state stays", await state(), ["10", "5"]);
check("the terminal says so", await heard("counter.vas: reloaded, state kept", since), true);
since = edit('(let step-text "1")', '(let step-text "2")');
check("a changed line starts again",
  await heard("counter.vas: reloaded; `step-text` started again", since), true);
check("the other names keep their values",
  await until(async () => JSON.stringify(await state()) === '["10","2"]'), true);
since = edit('[:h1 "Live counter"]', '[:h1 (html/text 5)]');
check("a save with a type error isn't taken",
  await heard("counter.vas: not taken, an error at ", since), true);
check("the terminal shows the error", await heard("type error:", since), true);
check("the page shows nothing", await text(".vastra-error"), null);
await click("+");
check("the old page still works", await state(), ["12", "2"]);
await open("/fixtures/counter/index.html");
check("reloaded meanwhile, it gets the last version that passed",
  await text("h1"), "Live counter");
since = edit('[:h1 (html/text 5)]', '[:h1 "Live counter"]');
check("the state stays", await state(), ["12", "2"]);
check("the terminal says so", await heard("counter.vas: reloaded, state kept", since), true);
since = edit("  (StepTyped String))", "  (StepTyped String)\n  Double)",
  "(on Reset", "(on Double\n  (set! total (* total 2))\n  @(save total))\n(on Reset",
  '[:button {:on-click Reset} "Reset"]', '[:button {:on-click Double} "Double"]');
check("a message type with a new constructor reaches the running program",
  await heard("counter.vas: reloaded; `Msg`", since), true);
await click("Double");
check("its new handler runs, on the names as they were", await state(), ["24", "2"]);
await evaluate("window.before = true");
since = terminal.length;
fs.appendFileSync(path.join(site, "fixtures/counter/index.html"), "\n<!-- edited -->\n");
check("editing index.html reloads the page",
  await until(async () => (await evaluate("window.before")) === undefined), true);
await heard("page connected", since);

console.log("vastra serve's terminal, a REPL into the page:");
check("an expression", await heard("3 : Int", ask("(+ 1 2)")), true);
check("a task runs in the page", await heard("42 : Int", ask("(task/map (task/succeed 41) inc)")), true);
const shown = await text(".count");
check("a name gives its live value", await heard(`${shown} : Int`, ask("total")), true);
check("*1 is that value", await heard(`${shown} : Int`, ask("*1")), true);
check(":dir marks the names that change, with their values",
  await heard(`total : Int  = ${shown}`, ask(":dir")), true);
ask("(set! total 100)");
check("set! changes the page", await until(async () => (await text(".count")) === "100"), true);
check("a value the program cannot take is rejected",
  await heard("type error:", ask('(set! total "a lot")')), true);
check("and the page is unchanged", await state(), ["100", "2"]);
ask("@(count-by! +)");
check("a ! function is like a click", await until(async () => (await text(".count")) === "102"), true);
since = terminal.length;
fs.appendFileSync(counterVas, "\n; saved again\n");
check("saving counter.vas keeps the state", await heard("counter.vas: reloaded, state kept", since), true);
check("the page still shows 102", await text(".count"), "102");
await type("3");
ask('(fn parse-step [text] (match (string/to-int (string/trim text)) [(Some n) (if (> n 2) (Err "Too big.") (Ok n))] [None (Err "The step must be a whole number.")]))');
check("a redefinition reaches the running page",
  await until(async () => (await text(".error")) === "Too big."), true);
check("the state stays", (await state())[1], "3");
check(":type", await heard("(Result String Int)", ask(':type (parse-step "1")')), true);
check("a rejected submission", await heard("type error:", ask("(parse-step 1)")), true);
// A view written at the prompt replaces the view of its place, until the
// file is saved again.
ask('(view "#app" (html [:h1 "replaced"]))');
check("a view at the prompt replaces the one of its place",
  await until(async () => (await text("h1")) === "replaced"), true);
fs.appendFileSync(counterVas, "\n; and again\n");
check("saving the file brings its own back", await until(async () => (await text("h1")) === "Live counter"), true);

// A type a macro writes changes when its file is saved.
console.log("changing types:");
since = terminal.length;
await open("/fixtures/grow/index.html");
await heard("page connected", since);
const growVas = path.join(site, "fixtures/grow/grow.vas");
await heard("same : (-> Mood Mood)", ask("(fn same [m::Mood] m)"));
since = rewrite(growVas, "(enum Mood Calm)", "(enum Mood Calm Busy)");
check("a type a macro writes changes when its file is saved", await heard("grow.vas: reloaded; `Mood`", since), true);
ask("(set! mood Busy)");
check("with its new constructor", await heard("Busy : Mood", ask("mood")), true);
check("code typed at the prompt that writes it takes the new one",
  await heard("Busy : Mood", ask("(same Busy)")), true);
check("a use at the prompt cannot change it",
  await heard("the type `Mood` changes only in its file", ask("(enum Mood Calm)")), true);

// A name its file leaves open: the prompt fixes its parts, a save keeps
// them, and a file that fixes one otherwise takes it over: that part resets.
console.log("a name's type fixed by its uses:");
since = terminal.length;
await open("/fixtures/open/index.html");
await heard("page connected", since);
const openVas = path.join(site, "fixtures/open/open.vas");
const typed = (value, type) => `${value} : ${type}`;
check("the file leaves it open", await heard(typed("{:lines [], :picked None}",
  "{:lines [?model], :picked (Option ?model1)}"), ask("model")), true);
ask('(set! model :lines ["from the prompt"])');
ask("(pick! 1)");
check("the prompt fixes it", await heard(typed('{:lines ["from the prompt"], :picked (Some 1)}',
  "{:lines [String], :picked (Option Int)}"), ask("model")), true);
since = rewrite(openVas, "(let model", "\n(let model");
check("saving the file keeps it", await heard("open.vas: reloaded, state kept", since), true);
check("as the prompt fixed it", await heard(typed('{:lines ["from the prompt"], :picked (Some 1)}',
  "{:lines [String], :picked (Option Int)}"), ask("model")), true);
since = rewrite(openVas, "(Some n)))", "(Some n)))\n(fn total! [] (sum (:lines model)))");
check("a file that fixes it otherwise takes it over", await heard("open.vas: reloaded; `model`", since), true);
check("and says what was reset",
  await heard("note: `model` changed type: :lines starts again from its new value", since), true);
check("the rest keeps its value", await heard(typed("{:lines [], :picked (Some 1)}",
  "{:lines [Int], :picked (Option Int)}"), ask("model")), true);

// A program in several files: the page loads its module from beside it,
// the view follows the module's names, and a saved module is reloaded.
console.log("a program in several files:");
since = terminal.length;
await open("/fixtures/files/index.html");
await heard("page connected", since);
const cartVas = path.join(site, "fixtures/files/shop/cart.vas");
const mainVas = path.join(site, "fixtures/files/main.vas");
const total = () => text("#total");
const totalIs = (shown) => until(async () => (await total()) === shown);
check("the module loads from beside the page", await total(), "total 0");
await click("Buy");
await click("Buy");
check("the view follows the module's names, changed by its ! function",
  await total(), "total 6");
ask('(set! cart/items [{:name "cake" :price 5}])');
check("and by the prompt", await totalIs("total 5"), true);
since = rewrite(cartVas, "(reduce + 0", "(* 2 (reduce + 0", "items)))", "items))))");
check("saving the module reloads it",
  await heard("shop/cart.vas: reloaded, state kept", since), true);
check("its names keep their values, under its new code", await totalIs("total 10"), true);
since = rewrite(cartVas, "(* 2 (reduce + 0", '(str "$" (reduce + 0');
check("a function of a new type",
  await heard("shop/cart.vas: reloaded; `total` changed type", since), true);
check("reaches the page's view, which uses it", await totalIs("total $5"), true);
since = rewrite(cartVas, "(fn total [items]", "(fn total [items tax]");
check("a save that breaks the page's file isn't taken",
  await heard("shop/cart.vas: not taken, an error in main.vas at ", since), true);
check("the page shows nothing", await text(".vastra-error"), null);
await click("Buy");
check("and keeps running", await total(), "total $8");
since = rewrite(cartVas, "(fn total [items tax]", "(fn total [items]");
check("fixing it reaches the page", await heard("shop/cart.vas: reloaded", since), true);
check("the state stays", await total(), "total $8");
since = rewrite(mainVas, "(on Empty (cart/clear!))", "(on Empty (set! cart/items []))");
check("another file cannot change the module's names",
  await heard("type error: `cart/items` changes only in its own file", since), true);
since = rewrite(mainVas, "(on Empty (set! cart/items []))", "(on Empty (cart/clear!))");
await heard("main.vas: reloaded", since);
await click("Empty");
check("it calls one of the module's ! functions", await total(), "total $0");
since = terminal.length;
await open("/fixtures/files/recording.html");
check("a recording refuses two files' names it can't tell apart",
  await heard("type error: a recording can't tell `cart/items` from `items`", since),
  true);

// A save restarts the values computed from a line that changed, through the
// functions that read them, and in the page when a module is saved.
console.log("vastra serve, the values computed from a line that changed:");
since = terminal.length;
await open("/fixtures/restart/index.html");
await heard("page connected", since);
const gridIs = (shown) => until(async () => (await text("main")) === shown);
check("the page shows the module's cell", await gridIs("cell 1cell 1"), true);
since = rewrite(path.join(site, "fixtures/restart/parts.vas"), "cell 1", "cell 2");
check("saving the module restarts the values computed from its cell",
  await heard("parts.vas: reloaded; `cell`, `cells`, `grid` started again", since), true);
check("so the page shows what its files say", await gridIs("cell 2cell 2"), true);
since = rewrite(path.join(site, "fixtures/restart/restart.vas"),
  "[:div cells]", '[:div cells [:p "end"]]');
check("a function whose line changed restarts only the values that call it",
  await heard("restart.vas: reloaded; `grid` started again", since), true);
check("which show its new code", await gridIs("cell 2cell 2end"), true);

// A save removes the names its file no longer defines, and the code typed at
// the prompt that uses them; a new ns starts the page again.
console.log("vastra serve, the names a save removes:");
const namesVas = path.join(site, "fixtures/names/names.vas");
// What :dir lists, once it has answered.
const listed = async () => {
  const at = ask(":dir");
  await heard(" : ", at);
  await sleep(300);
  return terminal.slice(at);
};
since = terminal.length;
await open("/fixtures/names/index.html");
await heard("page connected", since);
await heard("doubled : ", ask("(fn doubled [] (* 2 score))"));
await heard("calm : ", ask("(fn calm [] Calm)"));
since = rewrite(namesVas, "(type Mood Calm Busy)\n", "", "(let score 2)\n", "");
check("deleting definitions removes the prompt's code that uses them, named",
  await heard("note: removed `doubled`, typed at the prompt, which used `score`", since),
  true);
check("a type's constructors too",
  await heard("note: removed `calm`, typed at the prompt, which used `Mood`", since),
  true);
let names = await listed();
check("and they are gone", ["game : Int", "score", "doubled", "Mood", "calm"]
  .map((name) => names.includes(name)), [true, false, false, false, false]);
since = rewrite(namesVas, "(let game 1)", "(let level 1)");
await heard("names.vas: reloaded", since);
names = await listed();
check("renaming one leaves only the new name",
  [names.includes("level : Int"), names.includes("game")], [true, false]);
since = rewrite(namesVas, "(let level 1)", "(ns names)\n(let level 1)");
check("adding an ns starts the page again",
  await heard("names.vas: started again, because its ns changed", since), true);
check(":dir shows no stale name", (await listed()).split("level : Int").length - 1, 1);

// JavaScript from a page: ES modules load before the program runs, and
// a callback runs as a handler does, given what its handover writes.
console.log("JavaScript from a page:");
since = terminal.length;
await open("/fixtures/js/index.html");
await heard("page connected", since);
check("a package in node_modules, and a module beside the page",
  await until(async () => (await text("#greeting")) === "hello, page"), true);
check("their answers decoded by the let's type", await text("#area"), "area 12");
await click("Count");
await click("Count");
check("a callback runs as a handler, and the view follows",
  await until(async () => (await text("#clicks")) === "clicks 2"), true);
await click("Misfit");
check("what doesn't fit runs the handover's clause instead, as a handler", await until(async () =>
  (await text("#problem")) === "in detail: expected a string, found a number"), true);
ask("(fn shifted [e] (:shiftKey e))");
check("a handler reading a key the handover doesn't write is a type error",
  await heard("type error: unexpected key :shiftKey",
    ask("(js/callback shifted [e::{:key String}] [(Err _) false])")), true);
check("a handover decoding with no clause is refused",
  await heard("syntax error: decoding a JavaScript value needs an (Err why) clause",
    ask("(js/callback inc [n::Int])")), true);
const greeted = ask('(js/to-json @(js/call greet ["prompt"]))');
check("an import is tried at the prompt",
  await heard('JString "hello, prompt")', greeted), true);

// A page's state changed from the prompt along paths, and by saving its file,
// with real mouse input.
console.log("a page's state, changed from the prompt:");
since = terminal.length;
await open("/fixtures/table/index.html");
await heard("page connected", since);
const table = () => evaluate(`[...document.querySelectorAll(".card")].map((c) => [c.textContent, c.className])`);
const looks = () => evaluate(`document.querySelector(".table").className`);
const centre = (selector) => evaluate(`(() => { const r = document.querySelector(${JSON.stringify(selector)}).getBoundingClientRect();
  return [r.x + r.width / 2, r.y + r.height / 2]; })()`);
const drag = async (selector, dx, dy) => {
  const [x, y] = await centre(selector);
  await mouse("mousePressed", x, y, "left", 1);
  await mouse("mouseMoved", x + dx, y + dy, "left", 1);
  await mouse("mouseReleased", x + dx, y + dy, "left", 0);
};
await drag(".card:nth-child(2)", 1, 0);
check("a press and a release turn a card over", (await table())[1][1], "card face-up");
await drag(".card:nth-child(2)", 1, 0);
check("another turns it back", (await table())[1][1], "card");
ask("(update! table :cards 2 :face-up not)");
check("update! along a path", await until(async () => (await table())[2][1] === "card face-up"), true);
ask('(set! table :cards 0 :name "zero")');
check("set! along a path", await until(async () => (await table())[0][0] === "zero"), true);
ask('(set! table :message "Changed.")');
check("set! a key", await until(async () => (await text(".message")) === "Changed."), true);
const feel = () => evaluate(`document.querySelector(".table").style.getPropertyValue("--sway")`);
check("a value of the wrong type is rejected", await heard("type error:", ask('(set! table :feel :sway "high")')), true);
check("and the page is unchanged", await feel(), "4.0");
ask("(set! table :feel :sway 10.0)");
check("set! a nested key", await until(async () => (await feel()) === "10.0"), true);
ask("(set! table :back Stars)");
check("set! a constructor", await until(async () => (await looks()) === "table stars"), true);
const before = await table();
since = terminal.length;
fs.appendFileSync(path.join(site, "fixtures/table/table.vas"), "\n;; saved again\n");
check("saving table.vas keeps the state", await heard("table.vas: reloaded, state kept", since), true);
check("the same cards, the same way up", await table(), before);
// Changing types in table.vas while the page runs.
const tableVas = path.join(site, "fixtures/table/table.vas");
since = rewrite(tableVas, "(type Back Woven Stars Checks)", "(type Back Woven Stars Checks Lattice)",
  '[Checks "checks"]))', '[Checks "checks"]\n    [Lattice "lattice"]))');
check("a type with a new constructor keeps the program running", await heard("table.vas: reloaded; `Back`", since), true);
check("and its state", await table(), before);
check("a value that still fits stays", await looks(), "table stars");
ask("(set! table :back Lattice)");
check("the new constructor can be chosen", await until(async () => (await looks()) === "table lattice"), true);
since = rewrite(tableVas, ":back    Woven", ':back    Woven\n   :theme   "dark"');
check("a key added to the state keeps the program running",
  await heard("table.vas: reloaded; `initial`", since), true);
check("the rest of the state survives", await table(), before);
check("the state has the new key, from the file", await heard('"dark" : String', ask("(:theme table)")), true);
check("and keeps its other keys", await looks(), "table lattice");

// Recording and replaying, from the REPL, with real mouse input. Each
// recording waits before its press, so a replay shows the names put back.
console.log("recording and replaying:");
const face = async (i) => (await table())[i][1];
check("with nothing recorded, stop says so",
  await heard("browser/NotRecording", ask("browser/stop")), true);
await heard("unit : Unit", ask("browser/record"));
await sleep(600);
await drag(".card:nth-child(2)", 1, 0);
ask("(let rec @browser/stop)");
ask('(fn kind [m] (match (:msg m) [(CardPressed _ _ _) "press"] [(PointerMoved _ _) "move"] [(PointerReleased _ _) "release"]))');
check("a recording holds the messages the handlers got, typed by the file",
  await heard('["press" "move" "release"] : [String]', ask("(map kind (:messages rec))")), true);
check("each at its time from the start, in seconds",
  await heard("true : Bool", ask("(let ats (map :at (:messages rec))) " +
    "(and (> (option/or (first ats) 0.0) 0.5) (< (reduce max 0.0 ats) 30.0))")), true);
await drag(".card:nth-child(2)", 1, 0);
check("turned back by hand", await face(1), "card");
ask("(browser/replay rec)");
check("a replay puts the names back and turns the card over again",
  await until(async () => (await face(1)) === "card face-up"), true);
await heard("unit : Unit", ask("(browser/loop rec)"));
ask("(set! table :feel :sway 7.0)");
check("a loop starts again from the recorded names",
  (await until(async () => (await face(1)) === "card face-up")) && (await until(async () => (await face(1)) === "card")), true);
check("keeping a change made meanwhile", await feel(), "7.0");
await mouse("mouseMoved", 5, 5, "none", 0);
await mouse("mouseMoved", 300, 200, "none", 0);
check("moves don't stop it; stop gives the recording, with the change",
  await heard(":sway 7.0", ask("browser/stop")), true);
await heard("unit : Unit", ask("(browser/loop rec)"));
await sleep(200);
const third = await face(2);
await drag(".card:nth-child(3)", 1, 0);
check("a press stops it, and reaches the program", (await face(2)) !== third, true);
check("then nothing is left to stop",
  await heard("browser/NotRecording", ask("browser/stop")), true);

// What a change of type in table.vas leaves behind.
console.log("what a change of type leaves behind:");
await heard("theme! : (-> String)", ask("(fn theme! [] (:theme table))"));
await heard("unit : Unit", ask("(browser/loop rec)"));
since = rewrite(tableVas, ':theme   "dark"', ':mood    "calm"');
check("a loop that is playing stops when a type changes, and says so",
  await heard("note: the replay stopped: the type of its names or messages changed", since), true);
check("a definition typed at the prompt that no longer checks is removed, and the REPL says so",
  await heard("note: removed `theme!`, typed at the prompt, which no longer checks: missing key :theme", since), true);
check("then nothing is left to stop",
  await heard("browser/NotRecording", ask("browser/stop")), true);
check("a recording made before keeps its type, which the program no longer takes",
  await heard("type error:", ask("(browser/replay rec)")), true);

// A page's REPL into itself (browser/submit): what it submits runs in its own
// session, so a definition it submits replaces the one its code uses.
console.log("a page's REPL into itself:");
await open("/fixtures/console/index.html");
const entries = () => evaluate(`[...document.querySelectorAll(".entry")].map((e) => e.textContent)`);
const prompt = () => evaluate(`document.querySelector("input").value`);
const enter = async (source) => {
  await type(source);
  await evaluate(`document.querySelector("form").requestSubmit()`);
};
await enter("(+ 1 2)");
check("it evaluates what is submitted",
  await until(async () => (await entries()).at(-1) === "(+ 1 2) 3 : Int"), true);
check("and clears the prompt", await prompt(), "");
check("its code uses its own rule", await text(".ruled"), "yes");
await enter("(fn rule [x] (< x 2))");
check("a definition it submits replaces the one its code uses",
  await until(async () => (await text(".ruled")) === "no"), true);
await enter("(fn rule [x] (mod x 2))");
check("a definition its code cannot take is refused",
  await until(async () => (await entries()).at(-1).includes("redefining `rule` breaks")), true);
check("and the one before stays", await text(".ruled"), "no");
await enter('(set! page :input "from the page")');
check("what it submits reaches the page's own state",
  await until(async () => (await prompt()) === "from the page"), true);

// Two pages: the REPL talks to the one whose tab came to the front last,
// also after the other reloads, and to the other once that one closes.
console.log("vastra serve, two pages:");
since = terminal.length;
await open("/fixtures/counter/index.html");
const second = (await send("Target.createTarget", { url: base + "/fixtures/counter/index.html" })).result.targetId;
const other = (await send("Target.attachToTarget", { targetId: second, flatten: true })).result.sessionId;
check("serve says which page the REPL talks to",
  await heard("page connected (2 open: the REPL talks to the one you last looked at)", since), true);
const count = (session) => evaluate(`document.querySelector(".count")?.textContent ?? null`, session);
// A page tells serve in a request of its own: give it the moment a person takes
// to reach the terminal.
const toFront = async (session) => {
  await evaluate(`window.dispatchEvent(new Event("focus"))`, session);
  await sleep(300);
};
const untouched = await count(other);
await toFront(sessionId);
ask("(set! total 7)");
check("the REPL talks to the page that came to the front",
  await until(async () => (await count(sessionId)) === "7"), true);
check("and not to the other", await count(other), untouched);
await toFront(other);
ask("(set! total 8)");
check("another page coming to the front takes it", await until(async () => (await count(other)) === "8"), true);
check("the first page is unchanged", await count(sessionId), "7");
since = terminal.length;
await page("Page.reload");
await heard("page connected", since);
const reloaded = await count(sessionId);
ask("(set! total 9)");
check("the other page reloading leaves the REPL where it was",
  await until(async () => (await count(other)) === "9"), true);
check("and the reloaded page is unchanged", await count(sessionId), reloaded);
// Leaving, a page says so (closing a tab also brings another to the front,
// which would hide whether it did); serve's ping would notice only seconds later.
await send("Page.navigate", { url: "about:blank" }, other);
await sleep(300);
ask("(set! total 10)");
check("a page that goes away hands the REPL to the one in front before",
  await until(async () => (await count(sessionId)) === "10"), true);
await send("Target.closeTarget", { targetId: second });

ws.close();
// Chrome's helper processes outlive the main one: end the whole group.
process.kill(-chrome.pid, "SIGKILL");
await sleep(300);
serve.kill();
for (const temporary of [profile, site, outside]) {
  try { fs.rmSync(temporary, { recursive: true, force: true }); } catch { /* a temporary file */ }
}
if (failures > 0) console.log(`The end of vastra serve's terminal:\n${terminal.slice(-2500)}`);
console.log(failures === 0 ? "all browser checks pass" : `${failures} browser check(s) failed`);
process.exit(failures === 0 ? 0 : 1);
