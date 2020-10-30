open Pacomb

(* blanks *)
let blank = Regexp.blank_regexp "\\([ \t\n\r]\\|[#][^\n]*\\)*"

let _ =
    let files = Args.files in
    List.iter (fun fn ->
        let f () = Grammar.parse_file Parser.main blank fn in
        Pos.handle_exception f ()
      ) files
