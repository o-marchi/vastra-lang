(* The terminal the REPL draws on: raw mode, the keys typed, and the
   terminal's answers. What is written is gathered by [emit] and sent by
   [flush], one write per frame. *)

let out = Buffer.create 4096
let emit = Buffer.add_string out

let flush () =
  let s = Buffer.contents out in
  Buffer.clear out;
  let rec write off =
    if off < String.length s then
      match Unix.write_substring Unix.stdout s off (String.length s - off) with
      | n -> write (off + n)
      | exception Unix.Unix_error (EINTR, _, _) -> write off
  in
  write 0

let cooked = lazy (Unix.tcgetattr Unix.stdin)

let raw () =
  Unix.tcsetattr Unix.stdin TCSAFLUSH
    {
      (Lazy.force cooked) with
      c_icanon = false;
      c_echo = false;
      c_isig = false;
      c_ixon = false;
      c_icrnl = false;
      c_vmin = 1;
      c_vtime = 0;
    };
  (* Pasted text comes marked, so its newlines don't submit it. The cursor is
     drawn as a cell, so the terminal's own stays hidden. *)
  emit "\027[?2004h\027[?25l";
  flush ()

let restore () =
  emit "\027[?2004l\027[0m\027[?25h";
  flush ();
  Unix.tcsetattr Unix.stdin TCSAFLUSH (Lazy.force cooked)

let resized = ref false

(* 28 is SIGWINCH on Linux and the BSDs; OCaml has no name for it. *)
let watch_size () = Sys.set_signal 28 (Sys.Signal_handle (fun _ -> resized := true))

type key =
  | Char of string
  | Enter
  | Newline
  | Tab
  | Backspace
  | Delete
  | Esc
  | Up
  | Down
  | Left
  | Right
  | Home
  | End
  | Ctrl of char
  | Paste of string
  | Unknown

let find ?(from = 0) s sub =
  let n = String.length sub in
  let rec go i =
    if i + n > String.length s then None
    else if String.sub s i n = sub then Some i
    else go (i + 1)
  in
  go from

(* The key at the start of [s] and its length, or None while more bytes are
   needed. *)
let parse s =
  let n = String.length s in
  match s.[0] with
  | '\r' -> Some (Enter, 1)
  | '\n' -> Some (Newline, 1)
  | '\t' -> Some (Tab, 1)
  | '\127' | '\b' -> Some (Backspace, 1)
  | '\027' when n = 1 -> None
  | '\027' when s.[1] = '\r' -> Some (Newline, 2)
  | '\027' when s.[1] = '[' || s.[1] = 'O' -> (
      let rec final i =
        if i >= n then None else if s.[i] >= '@' && s.[i] <= '~' then Some i else final (i + 1)
      in
      match final 2 with
      | None -> None
      | Some i -> (
          let len = i + 1 in
          match (String.sub s 2 (i - 2), s.[i]) with
          | "200", '~' -> (
              match find ~from:len s "\027[201~" with
              | None -> None
              | Some e -> Some (Paste (String.sub s len (e - len)), e + 6))
          | _, 'A' -> Some (Up, len)
          | _, 'B' -> Some (Down, len)
          | _, 'C' -> Some (Right, len)
          | _, 'D' -> Some (Left, len)
          | _, 'H' | ("1" | "7"), '~' -> Some (Home, len)
          | _, 'F' | ("4" | "8"), '~' -> Some (End, len)
          | "3", '~' -> Some (Delete, len)
          | _ -> Some (Unknown, len)))
  | '\027' -> Some (Esc, 1)
  | c when Char.code c < 32 -> Some (Ctrl (Char.chr (Char.code c + 96)), 1)
  | c ->
      let len = if c >= '\xf0' then 4 else if c >= '\xe0' then 3 else if c >= '\xc0' then 2 else 1 in
      if n < len then None else Some (Char (String.sub s 0 len), len)

let pending = ref "" (* bytes read, not yet keys *)

let ready fd timeout =
  match Unix.select [ fd ] [] [] timeout with
  | r, _, _ -> r <> []
  | exception Unix.Unix_error (EINTR, _, _) -> false

let read () =
  let b = Bytes.create 4096 in
  match Unix.read Unix.stdin b 0 4096 with
  | n -> pending := !pending ^ Bytes.sub_string b 0 n
  | exception Unix.Unix_error (EINTR, _, _) -> ()

(* The next key typed, if one has come in full. A lone ESC is Esc, unless the
   rest of a sequence follows at once. *)
let rec key () =
  if !pending = "" then None
  else
    match parse !pending with
    | Some (k, n) ->
        pending := String.sub !pending n (String.length !pending - n);
        Some k
    | None when !pending = "\027" ->
        if ready Unix.stdin 0.03 then (
          read ();
          key ())
        else (
          pending := "";
          Some Esc)
    | None -> None

(* The cursor's row and column, from 0, as the terminal answers \e[6n; keys
   typed meanwhile stay pending. None if it does not answer. *)
let position () =
  emit "\027[6n";
  flush ();
  let deadline = Unix.gettimeofday () +. 0.5 in
  let rec answer from =
    match find ~from !pending "\027[" with
    | None -> None
    | Some i -> (
        let rest = String.sub !pending i (String.length !pending - i) in
        match Scanf.sscanf rest "\027[%u;%uR%n" (fun r c n -> (r, c, n)) with
        | r, c, n ->
            pending := String.sub !pending 0 i ^ String.sub rest n (String.length rest - n);
            Some (r - 1, c - 1)
        | exception _ -> answer (i + 1))
  in
  let rec wait () =
    match answer 0 with
    | Some p -> Some p
    | None when Unix.gettimeofday () < deadline ->
        if ready Unix.stdin 0.05 then read ();
        wait ()
    | None -> None
  in
  wait ()

(* The background colour, asked before the cursor's position: terminals answer
   in order, so the answer, if any, is pending once the position has come. *)
let ask_background () = emit "\027]11;?\027\\"

let background () =
  match find !pending "\027]11;rgb:" with
  | None -> None
  | Some i -> (
      let rest = String.sub !pending i (String.length !pending - i) in
      let hex h = int_of_string ("0x" ^ String.sub (h ^ h) 0 2) in
      match Scanf.sscanf rest "\027]11;rgb:%[0-9a-fA-F]/%[0-9a-fA-F]/%[0-9a-fA-F]%n" (fun r g b n -> (r, g, b, n)) with
      | r, g, b, n ->
          (* Ended by BEL or by ESC \ *)
          let len = String.length rest in
          let n = min len (if n < len && rest.[n] = '\007' then n + 1 else n + 2) in
          pending := String.sub !pending 0 i ^ String.sub rest n (len - n);
          Some (hex r, hex g, hex b)
      | exception _ -> None)

(* The window's rows and columns: the cursor goes as far as it can, says where
   it is, and comes back (ESC 7 and ESC 8 save and restore it). *)
let size () =
  emit "\0277\027[999;999H";
  let p = position () in
  emit "\0278";
  Option.map (fun (r, c) -> (r + 1, c + 1)) p
