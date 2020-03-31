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

let x2 = x ** x
let y2 = y ** y
let z2 = z ** z
let t2 = t ** t

let sphere =  x2 ++ y2 ++ z2 -- t2
let _ = Printf.printf "sphere = %a\n%!" print_polynome sphere
let t1 = triangulation sphere

let xmt = x -- t
let ymt = y -- t
let zmt = z -- t
let xmt2 = xmt ** xmt
let ymt2 = ymt ** ymt
let zmt2 = zmt ** zmt
let sphere2 = xmt2 ++ ymt2 ++ zmt2 -- t2
let _ = Printf.printf "sphere2 = %a\n%!" print_polynome sphere2
let t1 = triangulation sphere2


let xmt = x -- t
let ymt = y -- t
let zmt = z -- t
let xmt2 = xmt ** xmt
let ymt2 = ymt ** ymt
let zmt2 = zmt ** zmt
let hyper2 = xmt2 ++ ymt2 -- zmt2 -- t2
let _ = Printf.printf "hyper2 = %a\n%!" print_polynome hyper2
let t1 = triangulation hyper2
