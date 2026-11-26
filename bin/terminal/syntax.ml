(* What each byte of the input is, for indenting and colouring it while it is
   typed, complete or not. *)

type cls = Space | Bracket | Str | Comment | Keyword | Number | Form | Name

let block_forms =
  [ "let"; "fn"; "macro"; "par/let"; "^let"; "if"; "when"; "match"; "do"; "later";
    "on"; "view"; "for"; "type"; "ns" ]

let delimiter c = String.contains " \t\n,()[]{}\";" c
let opening c = c = '(' || c = '[' || c = '{'

let classify src =
  let n = String.length src in
  let a = Array.make n Space in
  let rec go i after_open =
    if i < n then (
      let fill cls j =
        Array.fill a i (j - i) cls;
        j
      in
      let c = src.[i] in
      let j =
        match c with
        | ' ' | '\t' | '\n' | ',' -> fill Space (i + 1)
        | '(' | ')' | '[' | ']' | '{' | '}' -> fill Bracket (i + 1)
        | ';' -> fill Comment (Option.value (String.index_from_opt src i '\n') ~default:n)
        | '"' ->
            let rec close k =
              if k >= n then n
              else if src.[k] = '\\' then close (k + 2)
              else if src.[k] = '"' then k + 1
              else close (k + 1)
            in
            fill Str (min n (close (i + 1)))
        | _ ->
            let rec stop k = if k < n && not (delimiter src.[k]) then stop (k + 1) else k in
            let j = stop i in
            let word = String.sub src i (j - i) in
            let digit k = k < j && src.[k] >= '0' && src.[k] <= '9' in
            fill
              (if c = ':' then Keyword
               else if c = '^' then Form (* parallel work, seen at a glance *)
               else if digit i || ((c = '-' || c = '+') && digit (i + 1)) then Number
               else if word = "true" || word = "false" then Number
               else if after_open && List.mem word block_forms then Form
               else Name)
              j
      in
      go j (c = '('))
  in
  go 0 false;
  a

(* The bracket matching the one at [i], skipping those in strings and comments. *)
let matching src cls i =
  let step = if opening src.[i] then 1 else -1 in
  let rec go j depth =
    if j < 0 || j >= String.length src then None
    else if cls.(j) <> Bracket then go (j + step) depth
    else if opening src.[j] = opening src.[i] then go (j + step) (depth + 1)
    else if depth = 0 then Some j
    else go (j + step) (depth - 1)
  in
  go (i + step) 0
