open Pacomb

(* blanks *)
let blank = Regexp.blank_regexp "\\([ \t\n\r]\\|[#][^\n]*\\)*"

let _ =
  let files = Args.files in
  Debug.set_debugs !Args.debug_string;
  List.iter (fun fn ->
      let f () = Grammar.parse_file Parser.main blank fn in
      Pos.handle_exception ~error:(fun e ->
          Printexc.print_backtrace stderr;
          raise e) f ()
    ) files
