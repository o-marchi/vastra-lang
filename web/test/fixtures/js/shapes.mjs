// A module beside the page, imported by page.vas and node.vas; an .mjs file,
// as npm packages often ship (vastra serve gives it its type).
export function area(w, h) { return w * h; }

// An object that holds itself, as an event holds its target: decoding reads
// only the keys its type names.
export function looped() { const o = { name: "loop" }; o.self = o; return o; }

// A property its prototype gives, as a KeyboardEvent's key.
export class Key { get key() { return "k"; } }
