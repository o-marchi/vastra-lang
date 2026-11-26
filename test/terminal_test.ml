(* The pure parts of the REPL's terminal: keys, indentation, history,
   brackets, the live area's rows, and results laid out for its width. *)

open Terminal

let failures = ref 0

let check name ok =
  if not ok then (
    incr failures;
    prerr_endline ("FAILED: " ^ name))

let () =
  check "an arrow" (Term.parse "\027[A" = Some (Term.Up, 3));
  check "a key in two parts waits" (Term.parse "\027[" = None);
  check "a character in UTF-8" (Term.parse "é!" = Some (Term.Char "é", 2));
  check "a paste waits for its end" (Term.parse "\027[200~(let a" = None);
  check "a paste" (Term.parse "\027[200~a\nb\027[201~x" = Some (Term.Paste "a\nb", 15));
  check "alt+enter is a new line" (Term.parse "\027\r" = Some (Term.Newline, 2));
  let indent s = Input.indent s (String.length s) in
  check "inside fn" (indent "(fn f [x]" = 2);
  check "under the first argument" (indent "(foo bar" = 5);
  check "a call with no argument yet" (indent "(foo" = 1);
  check "inside a vector" (indent "[1 2" = 1);
  check "brackets in strings don't count" (indent "(f \"(\" " = 3);
  check "on a later line" (indent "(fn f [x]\n  (+ x" = 5);
  check "inside ^let" (indent "(^let [a 1]" = 2);
  check "a clause's lines under its pattern" (indent "(match x\n  [(Some y)" = 3);
  check "a cond's clauses two in" (indent "(cond" = 2);
  check "or under the first clause" (indent "(cond [(< x 0) 1]" = 6);
  check "^map stands out" ((Syntax.classify "(^map f xs)").(1) = Syntax.Form);
  let hex = Syntax.classify "(+ 0xff -0x1a)" in
  check "hex is a number" (List.for_all (fun i -> hex.(i) = Syntax.Number) [ 3; 6; 8; 12 ]);
  let paste = Input.create () in
  Input.paste paste "a\r\nb\rc";
  check "pasted line ends" (paste.text = "a\nb\nc");
  let h = Input.history [ "(map sq [1])"; "(sq 2)"; "(f (sq 3))"; "(let a 1)" ] in
  let older () = Input.older h "(sq" in
  check "starting with what was typed first" (older () = Some "(sq 2)");
  check "then containing it" (older () = Some "(f (sq 3))");
  check "then nothing" (older () = None);
  check "back down" (Input.newer h = Some "(sq 2)");
  check "down to what was typed" (Input.newer h = Some "(sq");
  check "escaped newlines and backslashes"
    (Input.unescape (Input.escape "(f \"a\\n\"\n  x)") = "(f \"a\\n\"\n  x)");
  let src = "(f \")\" [1 (g)])" in
  let cls = Syntax.classify src in
  check "the matching bracket skips strings" (Syntax.matching src cls 0 = Some 14);
  check "and works backwards" (Syntax.matching src cls 12 = Some 10);
  (* The rows fit the window, so the terminal never wraps them. *)
  let rows =
    Area.rows ~width:40 ~top:[] ~busy:false ~below:[]
      ~input:(fun w -> [ Look.text Look.plain (String.make w 'x') ])
      ~status:(Some (Look.text Look.plain "left", Look.text Look.plain "right"))
  in
  check "rows fit" (List.for_all (fun r -> Look.width r <= 39) rows);
  let shows s r = Term.find (String.concat "" (List.map (fun (c : Look.cell) -> c.ch) r)) s <> None in
  check "the status line is there" (List.exists (shows "right") rows);
  let items = List.init 9 (fun i -> (string_of_int i, [])) in
  let shown sel = List.length (Area.menu_rows items sel) in
  check "a menu shows six, then how many more" (shown 0 = 7);
  check "and follows the choice to the end" (shown 8 = 6);
  Term.pending := "\027]11;rgb:eeee/e8e8/dddd\007\027[5;1R";
  check "the ground's colour" (Term.background () = Some (238, 232, 221));
  check "and the answer is taken" (!Term.pending = "\027[5;1R");
  Term.pending := "\027]11;rgb:10/12/10\027\\x";
  check "two digits, ended by ESC \\" (Term.background () = Some (16, 18, 16) && !Term.pending = "x");
  Theme.choose (Some (238, 232, 221));
  check "a light ground gets the light colours" (Theme.ink () = Theme.linen.ink);
  check "the waiting line is narrow" (Look.width (Waiting.row ~elapsed:3.) < 30);
  check "every pose of the creature is five wide"
    (List.for_all
       (fun p ->
         List.for_all (fun t -> Look.width (Creature.cells p t) = 5) [ 0.; 0.3; 0.6; 0.9 ])
       [ Resting; Waving; Weaving; Cheering; Spinning; Drooping; Asleep; Looking ]);
  (* Results laid out by their shape. *)
  let shown ?prev value ty = Show.result ?prev ~width:60 value ty in
  let rows r = match r with Some (rows, _, _) -> List.length rows | None -> -1 in
  check "one line when it fits" (rows (shown "[1 2 3]" "[Int]") = 1);
  let table = "[{:name \"Ada\", :age 36} {:name \"Grace\", :age 85}]" in
  check "records make a table: caption, keys, rows"
    (rows (shown table "[{:name String, :age Int, :and-a-long-key-to-be-too-wide Int}]") = 4);
  check "a shape left as printed" (shown "(Leaf 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25)" "Tree" = None);
  let many = "[" ^ String.concat " " (List.init 999 (fun i -> string_of_int (i + 1))) ^ "]" in
  (match shown many "[Int]" with
  | Some (rows, _, more) -> check "a tall result folds, and ↓ has more" (List.length rows <= 11 && more)
  | None -> check "a tall result folds" false);
  check "records in a type shorten, innermost first"
    (Show.elide "[{:a Int, :b {:c Int}}]" = "[{:a Int, :b {…}}]"
    && Show.elide "[{:a Int, :b {…}}]" = "[{…}]");
  let read s = match Vastra.Reader.read_all s with Ok [ n ] -> n | _ -> assert false in
  check "what changed is counted" (Show.differ (read "[{:a 1, :b 2} {:a 3, :b 4}]") (read "[{:a 1, :b 2} {:a 3, :b 5}]") = 1);
  (* Opening a value: the input holds the code for what is shown. *)
  let requests = read "[{:path \"/a\", :ms 35} {:path \"/b\", :ms 120}]" in
  Explore.opening ~steps:[ Explore.At 1; Explore.Key (read ":ms") ] (Some ("requests", requests));
  check "a path's code" (Explore.code () = "(get requests 1 :ms)");
  Explore.opening (Some ("requests", requests));
  ignore (Explore.key (Char "2"));
  ignore (Explore.key (Char "2"));
  check "a table sorted by its second column" (Explore.code () = "(sort-by :ms > requests)");
  ignore (Explore.key Down);
  ignore (Explore.key Right);
  check "the second row shown is the first value" (Explore.code () = "(get requests 0)");
  let session = Vastra.Session.create () in
  let eval src = List.map Vastra.Session.text (Vastra.Session.respond session "eval" src) in
  ignore (eval "(let n 1)");
  check "a check gives types"
    (List.map Vastra.Session.text (Vastra.Session.respond session "check" "(let n \"x\") (+ 1 2)")
    = [ "n : String"; " : Int" ]);
  check "and keeps nothing" (eval "n" = [ "1 : Int" ]);
  (* Results laid out for the window's width. *)
  let shown width src =
    match Vastra.Session.respond session ("eval " ^ string_of_int width) src with
    | [ Vastra.Session.Outcome o ] -> Vastra.Session.outcome_to_string ~width o
    | _ -> "?"
  in
  check "what fits stays on one line" (shown 30 "[1 2 3]" = "[1 2 3] : [Int]");
  check "a map that doesn't fit has a key per line, aligned"
    (shown 12 "{:a 1 :b [1 2]}" = "{:a 1,\n :b [1 2]}\n: {:a Int,\n   :b [Int]}");
  check "arguments align after the head"
    (shown 18 "(Some {:a 1 :b 2})"
    = "(Some {:a 1,\n       :b 2})\n: (Option {:a Int,\n           :b Int})");
  check "the closings that follow count"
    (shown 10 "[[1 2 3 4]]" = "[[1\n  2\n  3\n  4]]\n: [[Int]]");
  check "without a width, one line"
    (List.map Vastra.Session.text (Vastra.Session.respond session "eval" "{:a 1 :b [1 2]}")
    = [ "{:a 1, :b [1 2]} : {:a Int, :b [Int]}" ]);
  if !failures > 0 then exit 1
