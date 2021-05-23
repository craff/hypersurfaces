open Printing
open Pacomb

(* blanks *)
let blank = Regexp.blank_regexp "\\([ \t\n\r]\\|[#][^\n]*\\)*"

let _ =
  let files = Args.files in
  Debug.set_debugs !Args.debug_string;
  let parse fn =
    printf "reading %S\n%!" fn;
    Grammar.parse_file Parser.main blank fn
  in
  List.iter
    (Pos.handle_exception ~error:(fun _ -> exit 1) parse)
    files;
  if not !Args.batch then
    while true do
      let l = read_line () in
      Grammar.parse_string Parser.main blank l
    done
