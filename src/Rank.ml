(** Compute the rank of an integer matrix *)
open Z
open Printing

let two = add one one
let half x = div x two
let dbl x = mul x two
let even x = logand x one = zero

let gcd a b =
  if a = zero && b = zero then invalid_arg "gcd";
  let rec fn a b =
    if a = zero then (b,zero,one ) else
    if b = zero then (a,one ,zero) else
    if a = one  then (one,one ,zero) else
    if b = one  then (one,zero,one ) else
    match even a, even b with
    | (true, true) -> let (d,u,v) = fn (half a) (half b) in
                      (dbl d, u, v)
    | (true, _   ) -> let a' = half a in
                      let (d,u,v) = fn a' b in
                      if even u then
                        (d, half u, v)
                      else
                        let u1 = half (u + b) in
                        let v1 = v - a' in
                        let u2 = half (u - b) in
                        let v2 = v + a' in
                        if max (abs u1) (abs v1) < max (abs u2) (abs v2) then
                          (d,u1,v1)
                        else
                          (d,u2,v2)
    | (_, true) -> gn a b
    | (_, _   ) -> if a <= b then
                     let (d,u,v) = fn (b - a) a in
                     (* u (b-a) + v a = d
                     (v - u) a + u  b =  d*)
                     (d, v - u,u)
                   else
                     gn a b
    and gn a b = let (d,u,v) = fn b a in (d,v,u)
  in
  let (d,u,v) = fn (abs a) (abs b) in
  let u = if a < zero then neg u else u in
  let v = if b < zero then neg v else v in
  assert (a mod d = zero);
  assert (b mod d = zero);
  assert (a * u + b * v = d
          || (printf "gcd : %s + %s * %s + %s = %s\n%!"
                (to_string a) (to_string u) (to_string b)
                (to_string v) (to_string d); false));
  (d,u,v)

(*
let _ =
  for i = 1 to 10000 do
    let a = Random.int 200_000_000  - 100_000_000 in
    let b = Random.int 200_000_000  - 100_000_000 in
    ignore (gcd a b)
  done
 *)

type line =
  | Elt of int * Z.t * line * int (** column, coef, rest, length *)
  | End

let print_mat ch =
  Array.iter (fun row ->
      fprintf ch "  ";
      let rec fn = function
        | End -> ()
        | Elt(i,x,l,_) -> fprintf ch "%d:%s " i (to_string x); fn l
      in
      fn row;
      print_newline ())

let length_row = function
    | Elt(_,_,_,s) -> s
    | End -> 0

let cons k x l = if x = zero then l else Elt(k,x,l, Stdlib.(length_row l + 1))

let getc l c = match l with
  | Elt(c',x,_,_) ->
     assert (c' >= c);
     if c = c' then x else zero
  | End -> zero

let kernel nbl nbc m =
  let mc = Array.make nbc [] in
  let k = ref 0 in
  let i1 = ref 0 in
  let i2 = ref 0 in
  let add_line l =
    match l with
    | End -> incr i1
    | Elt(c,_,_,_) -> mc.(c) <- l :: mc.(c)
  in
  Array.iter add_line m;
  let fn u l1 v l2 =
    let rec fn l1 l2 =
      match (l1,l2) with
      | (Elt(k1,s1,l1,_), Elt(k2,s2,l2,_)) when k1 = k2 ->
         cons k1 (u*s1 + v*s2) (fn l1 l2)
      | (Elt(k1,s1,l1,_), Elt(k2,_,_,_)) when k1 < k2 ->
         cons k1 (u*s1) (fn l1 l2)
      | (Elt(_,_,_,_), Elt(k2,s2,l2,_)) (*when k1 > k2*) ->
         cons k2 (v*s2) (fn l1 l2)
      | (Elt(k1,s1,l1,_), End) ->
         cons k1 (u*s1) (fn l1 l2)
      | (End, Elt(k2,s2,l2,_)) ->
         cons k2 (v*s2) (fn l1 l2)
      | (End, End) -> End
    in fn l1 l2
  in

  let comb_line l1 u l2 v =
    fn u l1 v l2
  in
  let comb_line2 l1 u a l2 v b =
    (fn u l1 v l2, fn a l1 b l2)
  in
  (*printf "start\n%!";*)
  while !i1 < nbl && !i2 < nbc do
    let ic = !i2 in
    let lines = mc.(ic) in
    match lines with
    | [] -> incr k; incr i2
    | pl::lines -> incr i1; incr i2;
    (*printf "loop %d %d =>\n%a\n%!" il ic print_mat m;*)
    let best  = (abs (getc pl ic), length_row pl) in
    let (lines,pl,_) = List.fold_left (fun (lines,pl,best) l ->
      let p = (abs (getc l ic), length_row l) in
      if fst p <> zero && (fst best = zero || p < best) then
        (pl::lines, l, p)
      else (l::lines,pl,best)) ([],pl,best) lines
    in
    let pl = List.fold_left (fun pl l ->
      let p = getc pl ic in
      assert (p <> zero);
      let q = getc l ic in
      assert (q <> zero);
      if q mod p <> zero then
        begin
          let (d,u,v) = gcd p q in
          let a = p / d in
          let b = q / d in
          assert (u * a + v * b = one);
          let (pl,l) = comb_line2 pl u (-b) l v a in
          assert (getc l ic = zero);
          add_line l;
          pl
        end
      else
        begin
          assert (q mod p = zero);
          let x = q / p in
          let l = comb_line l one pl (-x) in
          assert (getc l ic = zero);
          add_line l;
          pl
        end) pl lines in
    mc.(ic) <- [pl]
  done;
  (*printf "end %d %d %d %d %d =>\n%a\n%!" nbl nbc !k !i1 !i2 print_mat m;*)
  Stdlib.(!k + nbc - !i2)

let rank nbl nbc m =
  let k = kernel nbl nbc m in
  (*printf "%a\n%!" print_int_matrix m;*)
  Stdlib.(k , nbc - k)
