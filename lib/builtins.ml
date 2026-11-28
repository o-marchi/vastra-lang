(* Implementations of the prelude's `native` declarations. Their types are in
   prelude.vas; the type checker guarantees the arguments. *)

open Value

let wrong name =
  raise (Internal (Printf.sprintf "`%s` received arguments of the wrong type" name))

let fn name run = (name, Builtin { builtin_name = name; run })
let some v = Ctor ("Some", [ v ])
let none = Ctor ("None", [])
let option = function Some v -> some v | None -> none
let call f args = !apply f args
let truthy name = function Bool b -> b | _ -> wrong name

let arith name zop fop iop =
  fn name (function
    | [ Int a; Int b ] -> Int (zop a b)
    | [ Float a; Float b ] -> Float (fop a b)
    | [ Fixed (f, a); Fixed (_, b) ] -> Fixed (f, Num.wrap f (iop a b))
    | _ -> wrong name)

(* IEEE comparisons on floats; the total order elsewhere. *)
let compare name zop fop =
  fn name (function
    | [ Float a; Float b ] -> Bool (fop a b)
    | [ a; b ] -> Bool (zop (Value.compare a b) 0)
    | _ -> wrong name)

(* A whole number of any type, as an Int. *)
let whole name = function Int n -> n | Fixed (f, x) -> Num.to_z f x | _ -> wrong name

(* A Float's whole part, toward zero, as C's cast drops it. NaN and the
   infinities have none and give 0, decided here, since OCaml's own
   conversions differ between native code and JavaScript. *)
let truncated x = if Float.is_finite x then Z.of_float x else Z.zero

let int_div name op =
  fn name (function
    | [ _; b ] when Z.equal (whole name b) Z.zero -> none
    | [ Int a; Int b ] -> some (Int (op a b))
    | [ Fixed (f, a); b ] -> some (Fixed (f, Num.of_z f (op (Num.to_z f a) (whole name b))))
    | _ -> wrong name)

(* to-u8 to to-i32 wrap a whole number, as C's casts do, and clamp a
   Float to the type's range. *)
let convert f =
  let name = "to-" ^ String.lowercase_ascii (Num.name (Fixed f)) in
  let low, high = Num.range f in
  fn name (function
    | [ Float x ] -> Fixed (f, Num.of_z f (Z.max low (Z.min high (truncated x))))
    | [ v ] -> Fixed (f, Num.of_z f (whole name v))
    | _ -> wrong name)

(* A size or index as an OCaml int; numbers beyond int range saturate. *)
let small n =
  if Z.fits_int n then Z.to_int n else if Z.sign n > 0 then max_int else min_int

(* bit/: an Int has endless bits; a fixed-width type keeps its own. *)
let bitwise name zop iop =
  fn name (function
    | [ Int a; Int b ] -> Int (zop a b)
    | [ Fixed (f, a); Fixed (_, b) ] -> Fixed (f, Num.wrap f (iop a b))
    | _ -> wrong name)

(* Shifting left by n multiplies by 2^n and rounds down; right by n is left by
   -n. A fixed-width type keeps no bits past 32, whichever way it shifts. *)
let shift name direction =
  let by n x =
    if Z.sign n >= 0 then Z.shift_left x (small n) else Z.shift_right x (small (Z.neg n))
  in
  fn name (function
    | [ Int x; Int n ] -> Int (by (Z.mul direction n) x)
    | [ Fixed (f, x); Int n ] ->
        let n = Z.max (Z.of_int (-32)) (Z.min (Z.of_int 32) (Z.mul direction n)) in
        Fixed (f, Num.of_z f (by n (Num.to_z f x)))
    | _ -> wrong name)

let rounding name op = fn name (function [ Float f ] -> Float (op f) | _ -> wrong name)
let vector name f = fn name (function [ Vector v ] -> f v | _ -> wrong name)
let of_list l = Vector (Array.of_list l)
let uchars s = Array.to_list (Diagnostic.uchars s)

(* Does [sep] occur in [s] at [i]? (Without allocating.) *)
let matches_at s i sep =
  let rec go k = k = String.length sep || (s.[i + k] = sep.[k] && go (k + 1)) in
  go 0

let form_list v = Array.to_list (Array.map (function Form n -> n | _ -> wrong "form") v)

(* Natives a platform adds (the browser runtime adds vastra.browser/record, ...). *)
let extra : (string * Value.t) list ref = ref []

(* Set by the program runner. *)
let program_args : string list ref = ref []
let exit_code = ref 0

(* How cli/exit ends the program: `vastra run` and built programs end
   then; at the prompt and in a page it only sets the status. *)
let ending = ref ignore

(* Where tasks print: stdout and stderr, unless the REPL's terminal shows it. *)
let print = ref print_endline
let print_error = ref prerr_endline
let run_task task k = match task with Task t -> t k | _ -> wrong "a task"

(* par/: [| f 0; ...; f (n - 1) |]. A native build computes it on every
   core (Rt.parallel); [f] is pure, so the result is the same. *)
let parallel : (int -> (int -> Value.t) -> Value.t array) ref = ref Array.init

let cores = Domain.recommended_domain_count () (* 1 in JavaScript *)

(* task/all, one task after another, everywhere: tasks change names. *)
let all_tasks tasks k =
  let results = Array.make (Array.length tasks) Unit in
  (* A task that finishes at once is followed from here, not from inside it, so
     the stack does not grow with the number of tasks (JavaScript's is small). *)
  let rec go i =
    if i = Array.length tasks then k (Ok (Vector results))
    else
      let running = ref true and finished = ref false in
      run_task tasks.(i) (function
        | Ok v ->
            results.(i) <- v;
            if !running then finished := true else go (i + 1)
        | Error e -> k (Error e));
      running := false;
      if !finished then go (i + 1)
  in
  go 0

(* A task's outcome as a value: Ok or Err. *)
let outcome = function Ok v -> Ctor ("Ok", [ v ]) | Error e -> Ctor ("Err", [ e ])

(* task/concurrent: each task starts when the one before has finished or
   waits for something outside the program, so tasks that wait, wait together.
   Each runs to the end, and it gives every outcome, in the tasks' order. A
   task that finishes at once returns here, so the stack stays flat. *)
let concurrent_tasks tasks k =
  let n = Array.length tasks in
  let outcomes = Array.make n Unit and left = ref n in
  if n = 0 then k (Ok (Vector outcomes))
  else
    Array.iteri
      (fun i task ->
        run_task task (fun r ->
            outcomes.(i) <- outcome r;
            decr left;
            if !left = 0 then k (Ok (Vector outcomes))))
      tasks

(* task/race and task/first-of: the tasks start in order, each in a running
   of its own; the first to end gives the outcome, and the others stop. One
   that ends at once leaves the rest unstarted, so in a tie the first written
   wins. A vector races in one loop, so a long one doesn't deepen the stack. *)
let race_tasks tasks k =
  let outer = !current in
  let runnings = Array.map (fun _ -> running ()) tasks in
  let forget = Array.map (fun r -> waiting outer (fun () -> stop r)) runnings in
  let ended = ref false in
  Array.iteri
    (fun i task ->
      if not !ended then
        within runnings.(i) (fun () ->
            run_task task (fun result ->
                if not !ended then (
                  ended := true;
                  Array.iter (fun f -> f ()) forget;
                  Array.iter stop runnings;
                  within outer (fun () -> k result)))))
    tasks

(* later: the task runs in a running of its own, which only stop! or the
   program's end stops. When it ends, the handler gets its outcome and
   runs as the program's, as a handler does. *)
let later task handler =
  Task
    (fun k ->
      let r = running () in
      within r (fun () ->
          run_task task (fun result ->
              within program (fun () ->
                  run_task (handler (outcome result)) (fun _ -> !Value.redraw ()))));
      k (Ok (Running r)))

(* The error kinds, whatever the platform's wording (OCaml's, or Node's under js_of_ocaml). *)
let file_error message =
  let says part = Util.contains (String.lowercase_ascii message) part in
  if says "no such file" || says "enoent" then Ctor ("vastra.file/NotFound", [])
  else if says "permission denied" || says "eacces" then
    Ctor ("vastra.file/PermissionDenied", [])
  else Ctor ("vastra.file/Other", [ Str message ])

let pad name side =
  fn name (function
    | [ Str s; Int n ] ->
        let missing = max 0 (small n - List.length (uchars s)) in
        let fill = String.make missing ' ' in
        Str (if side = `Left then fill ^ s else s ^ fill)
    | _ -> wrong name)

let entropy = lazy (Random.State.make_self_init ())

let all =
  [
    arith "+" Z.add ( +. ) Int32.add;
    arith "-" Z.sub ( -. ) Int32.sub;
    arith "*" Z.mul ( *. ) Int32.mul;
    fn "/" (function [ Float a; Float b ] -> Float (a /. b) | _ -> wrong "/");
    fn "macro/negate" (function
      | [ Int n ] -> Int (Z.neg n)
      | [ Float x ] -> Float (Float.neg x)
      | [ Fixed (f, x) ] -> Fixed (f, Num.wrap f (Int32.neg x))
      | _ -> wrong "-");
    int_div "quot" Z.div;
    int_div "mod" Z.erem;
    fn "=" (function [ a; b ] -> Bool (Value.equal a b) | _ -> wrong "=");
    compare "<" ( < ) ( < );
    compare ">" ( > ) ( > );
    compare "<=" ( <= ) ( <= );
    compare ">=" ( >= ) ( >= );
    (* Floats ignore NaN, and -0.0 is below 0.0, as C23's fmaximum_num. *)
    fn "max" (function
      | [ Float a; Float b ] -> Float (Float.max_num a b)
      | [ a; b ] -> if Value.compare a b >= 0 then a else b
      | _ -> wrong "max");
    fn "min" (function
      | [ Float a; Float b ] -> Float (Float.min_num a b)
      | [ a; b ] -> if Value.compare a b <= 0 then a else b
      | _ -> wrong "min");
    fn "not" (function [ Bool b ] -> Bool (not b) | _ -> wrong "not");
    fn "to-float" (function [ v ] -> Float (Z.to_float (whole "to-float" v)) | _ -> wrong "to-float");
    fn "to-int" (function
      | [ Float x ] -> Int (truncated x)
      | [ v ] -> Int (whole "to-int" v)
      | _ -> wrong "to-int");
    bitwise "bit/and" Z.logand Int32.logand;
    bitwise "bit/or" Z.logor Int32.logor;
    bitwise "bit/xor" Z.logxor Int32.logxor;
    fn "bit/not" (function
      | [ Int x ] -> Int (Z.lognot x)
      | [ Fixed (f, x) ] -> Fixed (f, Num.wrap f (Int32.lognot x))
      | _ -> wrong "bit/not");
    shift "bit/shift-left" Z.one;
    shift "bit/shift-right" Z.minus_one;
    rounding "round" Float.round;
    rounding "floor" Float.floor;
    rounding "ceil" Float.ceil;
    rounding "truncate" Float.trunc;
    rounding "sqrt" Float.sqrt;
    fn "abs" (function
      | [ Int n ] -> Int (Z.abs n)
      | [ Float x ] -> Float (Float.abs x)
      | [ Fixed (f, x) ] -> Fixed (f, if Num.signed f then Num.wrap f (Int32.abs x) else x)
      | _ -> wrong "abs");
    fn "to-string" (function [ v ] -> Str (to_display v) | _ -> wrong "to-string");
    fn "pr-str" (function [ v ] -> Str (to_string v) | _ -> wrong "pr-str");
    fn "string-append" (function
      | [ Str a; Str b ] -> Str (a ^ b)
      | _ -> wrong "string-append");
    ("unit", Unit);
    (* Vectors *)
    vector "count" (fun v -> Int (Z.of_int (Array.length v)));
    vector "empty?" (fun v -> Bool (Array.length v = 0));
    fn "conj" (function
      | [ Vector v; x ] -> Vector (Array.append v [| x |])
      | _ -> wrong "conj");
    fn "cons" (function
      | [ x; Vector v ] -> Vector (Array.append [| x |] v)
      | _ -> wrong "cons");
    fn "vector/concat" (function
      | [ Vector a; Vector b ] -> Vector (Array.append a b)
      | _ -> wrong "concat");
    fn "nth" (function
      | [ Vector v; Int i ] ->
          option
            (if Z.sign i >= 0 && Z.lt i (Z.of_int (Array.length v)) then
               Some v.(Z.to_int i)
             else None)
      | _ -> wrong "nth");
    vector "first" (fun v -> option (if Array.length v > 0 then Some v.(0) else None));
    fn "take" (function
      | [ Int n; Vector v ] ->
          Vector (Array.sub v 0 (max 0 (min (Array.length v) (small n))))
      | _ -> wrong "take");
    fn "drop" (function
      | [ Int n; Vector v ] ->
          let n = max 0 (min (Array.length v) (small n)) in
          Vector (Array.sub v n (Array.length v - n))
      | _ -> wrong "drop");
    fn "range" (function
      | [ Int a; Int b ] ->
          of_list
            (List.init (max 0 (small (Z.sub b a))) (fun i -> Int (Z.add a (Z.of_int i))))
      | _ -> wrong "range");
    fn "map" (function
      | [ f; Vector v ] -> Vector (Array.map (fun x -> call f [ x ]) v)
      | _ -> wrong "map");
    fn "par/map" (function
      | [ f; Vector v ] -> Vector (!parallel (Array.length v) (fun i -> call f [ v.(i) ]))
      | _ -> wrong "par/map");
    fn "map-indexed" (function
      | [ f; Vector v ] ->
          Vector (Array.mapi (fun i x -> call f [ Int (Z.of_int i); x ]) v)
      | _ -> wrong "map-indexed");
    fn "filter" (function
      | [ f; Vector v ] ->
          of_list
            (List.filter (fun x -> truthy "filter" (call f [ x ])) (Array.to_list v))
      | _ -> wrong "filter");
    fn "par/filter" (function
      | [ f; Vector v ] ->
          let keep = !parallel (Array.length v) (fun i -> call f [ v.(i) ]) in
          of_list (List.filteri (fun i _ -> truthy "par/filter" keep.(i)) (Array.to_list v))
      | _ -> wrong "par/filter");
    fn "remove" (function
      | [ f; Vector v ] ->
          of_list
            (List.filter
               (fun x -> not (truthy "remove" (call f [ x ])))
               (Array.to_list v))
      | _ -> wrong "remove");
    fn "reduce" (function
      | [ f; init; Vector v ] -> Array.fold_left (fun acc x -> call f [ acc; x ]) init v
      | _ -> wrong "reduce");
    fn "par/reduce" (function
      | [ f; empty; Vector v ] ->
          (* Halving: the first half, then the rest. The halves of the top
             levels go to [parallel], until they are about n / cores long. *)
          let rec tree lo hi =
            if hi - lo = 1 then v.(lo)
            else
              let mid = lo + ((hi - lo) / 2) in
              let half i = if i = 0 then tree lo mid else tree mid hi in
              let halves =
                if (hi - lo) * cores > Array.length v then !parallel 2 half
                else [| half 0; half 1 |]
              in
              call f [ halves.(0); halves.(1) ]
          in
          if Array.length v = 0 then empty else tree 0 (Array.length v)
      | _ -> wrong "par/reduce");
    vector "sort" (fun v -> of_list (List.stable_sort Value.compare (Array.to_list v)));
    fn "sort-by" (function
      | [ key; before; Vector v ] ->
          let keyed = List.map (fun x -> (call key [ x ], x)) (Array.to_list v) in
          let order (a, _) (b, _) =
            if truthy "sort-by" (call before [ a; b ]) then -1
            else if truthy "sort-by" (call before [ b; a ]) then 1
            else 0
          in
          of_list (List.map snd (List.stable_sort order keyed))
      | _ -> wrong "sort-by");
    vector "frequencies" (fun v ->
        Dict
          (Array.fold_left
             (fun d x ->
               let n =
                 match List.assoc_opt x d with Some (Int n) -> Z.succ n | _ -> Z.one
               in
               dict_insert x (Int n) d)
             [] v));
    fn "result/partition" (function
      | [ Vector v ] ->
          let pick tag =
            of_list
              (List.filter_map
                 (function Ctor (t, [ x ]) when t = tag -> Some x | _ -> None)
                 (Array.to_list v))
          in
          Record [ ("ok", pick "Ok"); ("err", pick "Err") ]
      | _ -> wrong "result/partition");
    (* Buffers: freeze gives the buffer's own array, which no one can
       change any more, since freeze uses the buffer up; to-vector copies it,
       since the buffer lives on. *)
    fn "buffer/repeat" (function
      | [ Int n; x ] -> Buffer (Array.make (max 0 (small n)) x)
      | _ -> wrong "buffer/repeat");
    vector "buffer/from" (fun v -> Buffer (Array.copy v));
    fn "buffer/freeze" (function [ Buffer v ] -> Vector v | _ -> wrong "buffer/freeze");
    fn "buffer/to-vector" (function
      | [ Buffer v ] -> Vector (Array.copy v)
      | _ -> wrong "buffer/to-vector");
    (* Dictionaries *)
    ("dict/empty", Dict []);
    fn "dict/insert" (function
      | [ k; v; Dict d ] -> Dict (dict_insert k v d)
      | _ -> wrong "dict/insert");
    fn "dict/get" (function
      | [ k; Dict d ] ->
          option
            (Option.map snd (List.find_opt (fun (k', _) -> Value.compare k k' = 0) d))
      | _ -> wrong "dict/get");
    fn "dict/count" (function
      | [ Dict d ] -> Int (Z.of_int (List.length d))
      | _ -> wrong "dict/count");
    fn "dict/entries" (function
      | [ Dict d ] ->
          of_list (List.map (fun (k, v) -> Record [ ("key", k); ("value", v) ]) d)
      | _ -> wrong "dict/entries");
    (* Tasks: [run] performs the work and gives Ok value or Err error. *)
    fn "task/succeed" (function
      | [ v ] -> Task (fun k -> k (Ok v))
      | _ -> wrong "task/succeed");
    fn "task/fail" (function
      | [ e ] -> Task (fun k -> k (Error e))
      | _ -> wrong "task/fail");
    fn "task/from-result" (function
      | [ Ctor ("Ok", [ v ]) ] -> Task (fun k -> k (Ok v))
      | [ Ctor ("Err", [ e ]) ] -> Task (fun k -> k (Error e))
      | _ -> wrong "task/from-result");
    fn "task/map" (function
      | [ Task t; f ] ->
          Task (fun k -> t (fun r -> k (Result.map (fun v -> call f [ v ]) r)))
      | _ -> wrong "task/map");
    fn "task/map-err" (function
      | [ Task t; f ] ->
          Task (fun k -> t (fun r -> k (Result.map_error (fun e -> call f [ e ]) r)))
      | _ -> wrong "task/map-err");
    fn "task/and-then" (function
      | [ Task t; f ] ->
          Task
            (fun k ->
              t (function Ok v -> run_task (call f [ v ]) k | Error e -> k (Error e)))
      | _ -> wrong "task/and-then");
    fn "task/all" (function
      | [ Vector tasks ] -> Task (fun k -> all_tasks tasks k)
      | _ -> wrong "task/all");
    fn "task/concurrent" (function
      | [ Vector tasks ] -> Task (fun k -> concurrent_tasks tasks k)
      | _ -> wrong "task/concurrent");
    fn "task/race" (function
      | [ a; b ] -> Task (fun k -> race_tasks [| a; b |] k)
      | _ -> wrong "task/race");
    fn "task/first-of" (function
      | [ Vector [||] ] -> Task (fun k -> k (Ok none))
      | [ Vector tasks ] ->
          Task (fun k -> race_tasks tasks (fun r -> k (Result.map some r)))
      | _ -> wrong "task/first-of");
    fn "macro/later" (function
      | [ task; handler ] -> later task (fun o -> call handler [ o ])
      | _ -> wrong "macro/later");
    fn "macro/later-dropping" (function
      | [ task ] -> later task (fun _ -> Task (fun k -> k (Ok Unit)))
      | _ -> wrong "macro/later-dropping");
    fn "stop!" (function
      | [ Running r ] ->
          stop r;
          Unit
      | _ -> wrong "stop!");
    ("task/ended", Running { stopped = true; waits = Hashtbl.create 0 });
    fn "task/recover" (function
      | [ Task t; f ] ->
          Task
            (fun k ->
              t (function Ok v -> k (Ok v) | Error e -> run_task (call f [ e ]) k))
      | _ -> wrong "task/recover");
    (* Files, the console and the command line (modules vastra.file, vastra.console, vastra.cli). *)
    fn "vastra.file/read-text" (function
      | [ Str path ] ->
          Task
            (fun k ->
              k
                (match In_channel.with_open_bin path In_channel.input_all with
                | s when String.is_valid_utf_8 s -> Ok (Str s)
                | _ ->
                    Error
                      (Ctor
                         ("vastra.file/Other", [ Str "the file is not valid UTF-8 text" ]))
                | exception Sys_error m -> Error (file_error m)))
      | _ -> wrong "read-text");
    fn "vastra.file/write-text" (function
      | [ Str path; Str text ] ->
          Task
            (fun k ->
              k
                (match
                   Out_channel.with_open_bin path (fun oc -> output_string oc text)
                 with
                | () -> Ok Unit
                | exception Sys_error m -> Error (file_error m)))
      | _ -> wrong "write-text");
    fn "vastra.console/print" (function
      | [ Str s ] ->
          Task
            (fun k ->
              !print s;
              k (Ok Unit))
      | _ -> wrong "print");
    fn "vastra.console/print-error" (function
      | [ Str s ] ->
          Task
            (fun k ->
              !print_error s;
              k (Ok Unit))
      | _ -> wrong "print-error");
    ("vastra.clock/now", Task (fun k -> k (Ok (Float (Unix.gettimeofday ())))));
    ("vastra.clock/elapsed", Task (fun k -> k (Ok (Float (!Clock.elapsed ())))));
    (* The platform's randomness, made once and drawn from for each seed. *)
    ( "vastra.random/seed",
      Task
        (fun k ->
          let bits = Random.State.bits32 (Lazy.force entropy) in
          k (Ok (Record [ ("state", Fixed (Num.U32, bits)) ]))) );
    (* NaN is not more than zero either: it returns at once. *)
    fn "vastra.clock/sleep" (function
      | [ Float s ] ->
          Task
            (fun k ->
              if s > 0. then
                wait (fun ended -> !Clock.after s (fun () -> ended (Ok Unit))) k
              else k (Ok Unit))
      | _ -> wrong "sleep");
    ( "vastra.cli/args",
      Task (fun k -> k (Ok (of_list (List.map (fun a -> Str a) !program_args)))) );
    fn "vastra.cli/exit" (function
      | [ Int n ] ->
          Task
            (fun k ->
              exit_code := small n;
              !ending ();
              k (Ok Unit))
      | _ -> wrong "exit");
    (* A child of html, as the elements and text it puts in its place. *)
    fn "vastra.html/child" (fun args ->
        let rec child = function
          | Str s -> [ Ctor ("vastra.html/Text", [ Str s ]) ]
          | Vector items -> List.concat_map child (Array.to_list items)
          | element -> [ element ]
        in
        match args with [ v ] -> of_list (child v) | _ -> wrong "child");
    fn "vastra.json/parse" (function [ Str s ] -> Json.parse s | _ -> wrong "parse");
    (* Forms: code as data, for macros. *)
    fn "form/view" (function
      | [ Form n ] -> (
          let forms items = Vector (Array.of_list (List.map (fun i -> Form i) items)) in
          match n.form with
          | Int i | Hex i -> Ctor ("IntView", [ Int i ])
          | Float f -> Ctor ("FloatView", [ Float f ])
          | Bool b -> Ctor ("BoolView", [ Bool b ])
          | Str s -> Ctor ("StringView", [ Str s ])
          | Symbol s -> Ctor ("SymbolView", [ Str s ])
          | Keyword k -> Ctor ("KeywordView", [ Str k ])
          | List items -> Ctor ("ListView", [ forms items ])
          | Vector items -> Ctor ("VectorView", [ forms items ])
          | Map entries ->
              Ctor
                ("MapView", [ forms (List.concat_map (fun (k, v) -> [ k; v ]) entries) ]))
      | _ -> wrong "form/view");
    fn "form/string" (function
      | [ Str s ] -> Form (made (Str s))
      | _ -> wrong "form/string");
    fn "form/int" (function [ Int i ] -> Form (made (Int i)) | _ -> wrong "form/int");
    fn "form/symbol" (function
      | [ Str s ] -> Form (made (Symbol s))
      | _ -> wrong "form/symbol");
    fn "form/list" (function
      | [ Vector v ] -> Form (made (List (form_list v)))
      | _ -> wrong "form/list");
    fn "form/vector" (function
      | [ Vector v ] -> Form (made (Vector (form_list v)))
      | _ -> wrong "form/vector");
    fn "form/map" (function
      | [ Vector v ] ->
          let rec pairs = function k :: v :: rest -> (k, v) :: pairs rest | _ -> [] in
          Form (made (Map (pairs (form_list v))))
      | _ -> wrong "form/map");
    fn "form/at" (function
      | [ Form built; Form given ] -> Form { built with span = given.span }
      | _ -> wrong "form/at");
    fn "gensym" (function
      | [ Str base ] ->
          incr gensyms;
          Form (made (Symbol (Printf.sprintf "%s__%d" base !gensyms)))
      | _ -> wrong "gensym");
    (* Strings: lengths and padding count Unicode characters. *)
    fn "string/length" (function
      | [ Str s ] -> Int (Z.of_int (List.length (uchars s)))
      | _ -> wrong "string/length");
    fn "string/split" (function
      | [ Str s; Str sep ] when sep <> "" ->
          let n = String.length sep in
          let rec go start i acc =
            if i + n > String.length s then
              List.rev (String.sub s start (String.length s - start) :: acc)
            else if matches_at s i sep then
              go (i + n) (i + n) (String.sub s start (i - start) :: acc)
            else go start (i + 1) acc
          in
          of_list (List.map (fun p -> Str p) (go 0 0 []))
      | [ Str s; Str _ ] -> of_list [ Str s ]
      | _ -> wrong "string/split");
    fn "string/lines" (function
      | [ Str s ] ->
          let lines = String.split_on_char '\n' s in
          let lines =
            match List.rev lines with "" :: rest -> List.rev rest | _ -> lines
          in
          of_list
            (List.map
               (fun l ->
                 Str
                   (if String.ends_with ~suffix:"\r" l then
                      String.sub l 0 (String.length l - 1)
                    else l))
               lines)
      | _ -> wrong "string/lines");
    fn "string/join" (function
      | [ Str sep; Vector v ] ->
          Str
            (String.concat sep
               (Array.to_list
                  (Array.map (function Str s -> s | _ -> wrong "string/join") v)))
      | _ -> wrong "string/join");
    fn "string/trim" (function
      | [ Str s ] -> Str (String.trim s)
      | _ -> wrong "string/trim");
    fn "string/blank?" (function
      | [ Str s ] -> Bool (String.trim s = "")
      | _ -> wrong "string/blank?");
    fn "string/to-int" (function
      | [ Str s ] ->
          let digits =
            if String.starts_with ~prefix:"-" s then String.sub s 1 (String.length s - 1)
            else s
          in
          option
            (if digits <> "" && String.for_all (fun c -> c >= '0' && c <= '9') digits then
               Some (Int (Z.of_string s))
             else None)
      | _ -> wrong "string/to-int");
    pad "string/pad-left" `Left;
    pad "string/pad-right" `Right;
    fn "string/fixed" (function
      | [ Float f; Int d ] when Float.is_finite f ->
          Str (Printf.sprintf "%.*f" (max 0 (min 100 (small d))) f)
      | [ Float f; Int _ ] -> Str (Util.float_to_string f)
      | _ -> wrong "string/fixed");
    fn "string/hex" (function
      | [ Int n ] -> Str (Z.format "%x" n)
      | [ Fixed (f, x) ] ->
          let bits = Num.bits f in
          let digits = Printf.sprintf "%%0%dx" (bits / 4) in
          Str (Z.format digits (Z.extract (Z.of_int32 x) 0 bits))
      | _ -> wrong "string/hex");
  ]
  @ List.map convert Num.fixed
