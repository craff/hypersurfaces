(*module R = Field.Q*)
module R = Field.Float
module D = Display.Make(R)
open D
module RX = HyperSurfaces.Make(R)
open RX
open R
open RX.Poly

let display scale ori (s,t) =
  let open Graphics in
  let _ = clear_graph () in
  set_color green;
  display scale ori t (fun x -> x);
  set_color black;
  display scale ori s (fun x -> x);
  ignore (input_char stdin)


let cst x = [[0;0;0], x]

let x = [[1;0;0], one]
let y = [[0;1;0], one]
let z = [[0;0;1], one]
let x2 = x ** x
let y2 = y ** y
let z2 = z ** z

let circle = x2 ++ y2 -- z2
let _ = Printf.printf "circle = %a\n%!" print_polynome circle
let t1 = triangulation circle

let _ = display 200.0 (0.,0.) t1

let ellipse = cst(of_int 10) ** x2 ++ y2 -- z2
let _ = Printf.printf "ellipse = %a\n%!" print_polynome ellipse
let t1 = triangulation ellipse

let _ = display 200.0 (0.,0.) t1

let xmz = x -- z
let ymz = y -- z
let xmz2 = xmz ** xmz
let ymz2 = ymz ** ymz
let circle2 = xmz2 ++ ymz2 -- z2
let _ = Printf.printf "circle2 = %a\n%!" print_polynome circle2
let t1 = triangulation circle2

let _ = display 200.0 (0.,0.) t1

let xmy = x -- y
let xpy = x ++ y
let xmy2 = xmy ** xmy
let xpy2 = xpy ** xpy
let ellipse2 = cst(of_int 50) ** xmy2 ++ xpy2 -- z2
let _ = Printf.printf "ellipse2 = %a\n%!" print_polynome ellipse2
let t1 = triangulation ellipse2

let _ = display 400.0 (0.,0.) t1

let xmz = x -- z
let ymz = y -- z
let xmz2 = xmz ** xmz
let ymz2 = ymz ** ymz
let ellipse3 = cst(of_int 4) ** xmz2 ++ ymz2 -- z2
let _ = Printf.printf "ellipse3 = %a\n%!" print_polynome ellipse3
let t1 = triangulation ellipse3

let _ = display 400.0 (0.,0.) t1

let quartic = circle ** circle ++ cst(of_int 1 /. of_int 2) ** x ** y ** (x -- y) ** (x ++ y)
let _ = Printf.printf "quartic = %a\n%!" print_polynome quartic
let t1 = triangulation quartic

let _ = display 400.0 (0.,0.) t1




(*
let ellipse4 = cst(of_int 50000000) ** xmz2 ++ ymz2 -- z2
let _ = Printf.printf "ellipse4 = %a\n%!" print_polynome ellipse4
let t1 = triangulation ellipse4

let ellipse5 = cst(of_int 500000) ** xmz2 ++ ymz2 -- z2
let _ = Printf.printf "ellipse5 = %a\n%!" print_polynome ellipse4
let t1 = triangulation ellipse5

 *)
