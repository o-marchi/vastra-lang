(* Prints an OCaml module embedding standard library files: each
   stdlib/NAME.vas becomes ("NAME", source). *)
let () =
  print_string "let files = [\n";
  Array.iteri
    (fun i path ->
      if i > 0 then
        Printf.printf "  (%S, {vastra|%s|vastra});\n"
          (Filename.remove_extension (Filename.basename path))
          (In_channel.with_open_bin path In_channel.input_all))
    Sys.argv;
  print_string "]\n\nlet find name = List.assoc_opt name files\n"
