module R = Field.Float
module RX = HyperSurfaces.Make(R)
open RX
open R
open RX.Poly

let cst x = [[0;0;0;0], x]
let x = [[1;0;0;0], one]
let y = [[0;1;0;0], one]
let z = [[0;0;1;0], one]
let t = [[0;0;0;1], one]
let t2 = t ** t
let xmt =  x -- t
let ymt =  y -- t
let zmt =  z -- t
let xmt2 = xmt ** xmt
let ymt2 = ymt ** ymt
let zmt2 = zmt ** zmt

let s a = xmt2 ++ cst one ** ymt2  ++ cst a ** ( ~-- t2 )
let s1 = s (of_int 9 /. of_int 10)
let s2 = s (of_int 5 /. of_int 10)

let _ = Printf.printf "s1 = %a, s2 = %a\n%!" print_polynome s1 print_polynome s2


let x2 = x ** x
let y2 = y ** y
let z2 = z ** z
let t2 = t ** t
let xpy = x ++ y
let xmy = x -- y
let xpy2 = xpy ** xpy
let xmy2 = xmy ** xmy
let xpypz = xpy ++ z
let xpypz2 = xpypz ** xpypz
let xpypz4 = xpypz2 ** xpypz2
let xpymz = xpy -- z
let xpymz2 = xpymz ** xpymz
let xpymz4 = xpymz2 ** xpymz2

open Simp

let r0 = zero
let r1 = one
let r2 = of_int 2
let r3 = of_int 3
let r4 = of_int 4

let p = x2 ++ y2 ++ cst 2.0 ** (x ** y)
let q,s = subdivise2 p R.(r1 /. r4) R.(r3 /. r4) 0 1
let _ = Printf.printf "p = %a\n=> q = %a,\n s = %a\n%!"
          print_polynome p print_polynome q print_polynome s
let q,s = subdivise2 p R.(r1 /. r2) R.(r1 /. r2) 0 1
let _ = Printf.printf "p = %a\n=> q = %a,\n s = %a\n%!"
          print_polynome p print_polynome q print_polynome s
let q,s = subdivise2 p R.(r3 /. r4) R.(r1 /. r4) 0 1
let _ = Printf.printf "p = %a\n=> q = %a,\n s = %a\n%!"
          print_polynome p print_polynome q print_polynome s

let p = x2 ++ cst 2.0 ** y2 -- cst 2.0 ** (x ** y)
let q,s = subdivise2 p R.(r1 /. r4) R.(r3 /. r4) 0 1
let _ = Printf.printf "p = %a\n=> q = %a,\n s = %a\n%!"
          print_polynome p print_polynome q print_polynome s
let q,s = subdivise2 p R.(r1 /. r2) R.(r1 /. r2) 0 1
let _ = Printf.printf "p = %a\n=> q = %a,\n s = %a\n%!"
          print_polynome p print_polynome q print_polynome s
let q,s = subdivise2 p R.(r3 /. r4) R.(r1 /. r4) 0 1
let _ = Printf.printf "p = %a\n=> q = %a,\n s = %a\n%!"
          print_polynome p print_polynome q print_polynome s

let cst x = [[0;0;0], x]

let x = [[1;0;0], one]
let y = [[0;1;0], one]
let z = [[0;0;1], one]

let p = x ++ y
let _ = Printf.printf "p = %a, p^4 = %a, p^10 = %a\n%!"
                      print_polynome p
                      print_polynome (pow p 4)
                      print_polynome (pow p 10)
let xmz = x -- z
let ymz = y -- z
let z2 = z ** z
let xmz2 = xmz ** xmz
let ymz2 = ymz ** ymz
let p = complete (cst(of_int 2) ** xmz2 ++ ymz2 -- z2)
let _ = Printf.printf "BEFORE\n%!"
let q,s = subdivise p  R.(r1 /. r4) R.(r3 /. r4) 0 1
let _ = Printf.printf "TEST1 p = %a\n=> q = %a,\n s = %a\n%!"
          print_polynome p print_polynome q print_polynome s
let q,s = subdivise2 p  R.(r1 /. r4) R.(r3 /. r4) 0 1
let _ = Printf.printf "TEST1 p = %a\n=> q = %a,\n s = %a\n%!"
          print_polynome p print_polynome q print_polynome s
let q,s = subdivise2 p  R.(r1 /. r2) R.(r1 /. r2) 0 1
let _ = Printf.printf "TEST2 p = %a\n=> q = %a,\n s = %a\n%!"
          print_polynome p print_polynome q print_polynome s
let q,s = subdivise2 p  R.(r3 /. r4) R.(r1 /. r4) 0 1
let _ = Printf.printf "TEST3 p = %a\n=> q = %a,\n s = %a\n%!"
          print_polynome p print_polynome q print_polynome s
