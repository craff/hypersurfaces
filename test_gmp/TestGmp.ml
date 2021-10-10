let loop1 n =
  let x = Mpfr.init () in
  let y = Mpfr.init () in
  let z = Mpfr.init () in
  ignore (Mpfr.set_si x 0 Mpfr.Near);
  ignore (Mpfr.set_si y 1 Mpfr.Near);
  for _ = 0 to n do
    (*Printf.printf "i:%d %s %s %s\n%!"
        i (Mpfr.to_string x)(Mpfr.to_string y)(Mpfr.to_string z);
     *)
    ignore (Mpfr.ui_div z 1 y Mpfr.Near);
    ignore (Mpfr.add x x z Mpfr.Near);
    ignore (Mpfr.add_ui y y 2 Mpfr.Near);
    ignore (Mpfr.ui_div z 1 y Mpfr.Near);
    ignore (Mpfr.sub x x z Mpfr.Near);
    ignore (Mpfr.add_ui y y 2 Mpfr.Near);
  done;
  ignore (Mpfr.mul_ui x x 4 Mpfr.Near);
  Printf.printf "res: %s\n%!" (Mpfr.to_string x)

let loop2 n =
  let x = ref (Mpfrf.of_int 0 Mpfr.Near) in
  let y = ref (Mpfrf.of_int 1 Mpfr.Near) in
  for _ = 0 to n do
    (*Printf.printf "i:%d %s %s %s\n%!"
        i (Mpfr.to_string x)(Mpfr.to_string y)(Mpfr.to_string z);
     *)
    x := Mpfrf.add !x (Mpfrf.ui_div 1 !y Mpfr.Near) Mpfr.Near;
    y := Mpfrf.add_int !y 2 Mpfr.Near;
    x := Mpfrf.sub !x (Mpfrf.ui_div 1 !y Mpfr.Near) Mpfr.Near;
    y := Mpfrf.add_int !y 2 Mpfr.Near;
  done;
  Printf.printf "res: %s\n%!" (Mpfr.to_string (Mpfrf.mul_ui !x 4 Mpfr.Near))

let loop0 n =
  let x = ref 0.0 in
  let y = ref 1.1 in
  for _ = 0 to n do
    (*Printf.printf "i:%d %s %s %s\n%!"
        i (Mpfr.to_string x)(Mpfr.to_string y)(Mpfr.to_string z);
     *)
    x := !x +. 1. /. !y;
    y := !y +. 2.;
    x := !x -. 1. /. !y;
    y := !y +. 2.;
  done;
  Printf.printf "res: %e\n%!" (!x *. 4.0)

let _ =
  if Array.length Sys.argv > 1 && Sys.argv.(1) = "f" then loop2 10000000
  else if Array.length Sys.argv > 1 && Sys.argv.(1) = "o" then loop0 10000000
  else loop1 10000000
