open Pacomb

(* blanks *)
let blank = Blank.from_charset (Charset.from_string " \t\n\r")

let _ =
    let files = Args.files in
    if files = [] then
      try
        while true do
          let f () =
            Printf.printf "=> %!"; (* initial prompt *)
            (* no need to stack the buffer of in_channel and those of Pacomb. So
               file descip  tor are preferred *)
            Grammar.parse_fd Parser.main blank Unix.stdin;
            raise End_of_file
          in
          (* [Pos] module provides a function to handle exception with
             an optional argument to call for error (default is to exit with
             code 1 *)
          Pos.handle_exception ~error:(fun _ -> ()) f ()
        done
      with
        End_of_file -> ()
    else
      List.iter (fun fn ->
          let fd = Unix.openfile fn [] 0o600 in
          let f () = Grammar.parse_fd Parser.main blank fd in
          Pos.handle_exception f ()
        ) files
