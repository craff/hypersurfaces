include Format

let print_array fn ch v =
  fprintf ch "(";
  Array.iteri (fun i x ->
      if i <> 0 then fprintf ch ", ";
      fn ch x) v;
  fprintf ch ")"

let print_list fn ch v =
  fprintf ch "(";
  List.iteri (fun i x ->
      if i <> 0 then fprintf ch ", ";
      fn ch x) v;
  fprintf ch ")"

let print_int_list ch l =
  let f ch = fprintf ch "%d" in
  print_list f ch l

(** a variant of sprintf that use its own internal buffer (more
   thread safe, if not partially applied), and that can use print_array
   and print_list above *)
let sprintf fmt =
  let buf = Buffer.create 128 in
  let formatter = formatter_of_buffer buf in
  kfprintf (fun ff -> pp_print_flush ff (); Buffer.contents buf) formatter fmt
