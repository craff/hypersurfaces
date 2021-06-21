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
  | Elt of int * Z.t * line
  | End

let print_mat ch =
  Array.iter (fun row ->
      fprintf ch "  ";
      let rec fn = function
        | End -> ()
        | Elt(i,x,l) -> fprintf ch "%d:%s " i (to_string x); fn l
      in
      fn row;
      print_newline ())

let snf nbl nbc m =
  let m = Array.copy m in
  let k = ref 0 in
  let swap_line i j =
    if i <> j then
      let tmp = m.(i) in
      m.(i) <- m.(j); m.(j) <- tmp
  in
  let cons k x l = if x = zero then l else Elt(k,x,l) in
  let fn u l1 v l2 =
    let rec fn l1 l2 =
      match (l1,l2) with
      | (Elt(k1,s1,l1), Elt(k2,s2,l2)) when k1 = k2 ->
         cons k1 (u*s1 + v*s2) (fn l1 l2)
      | (Elt(k1,s1,l1), Elt(k2,_,_)) when k1 < k2 ->
         cons k1 (u*s1) (fn l1 l2)
      | (Elt(k1,_,_), Elt(k2,s2,l2)) (*when k1 > k2*) ->
         cons k2 (v*s2) (fn l1 l2)
      | (Elt(k1,s1,l1), End) ->
         cons k1 (u*s1) (fn l1 l2)
      | (End, Elt(k2,s2,l2)) ->
         cons k2 (v*s2) (fn l1 l2)
      | (End, End) -> End
    in fn l1 l2
  in

  let comb_line i u j v =
    m.(i) <- fn u m.(i) v m.(j)
  in
  let comb_line2 i u a j v b =
    let l1 = m.(i) in
    let l2 = m.(j) in
    m.(i) <- fn u l1 v l2;
    m.(j) <- fn a l1 b l2
  in
  let getc l c = match l with
    | Elt(c',x,_) ->
       assert (c' >= c);
       if c = c' then x else zero
    | End -> zero
  in
  let i1 = ref 0 in
  let i2 = ref 0 in
  (*printf "start\n%!";*)
  while !i1 < nbl && !i2 < nbc do
    let il = !i1 in
    let ic = !i2 in
    (*printf "loop %d %d =>\n%a\n%!" il ic print_mat m;*)
    let best_j = ref il in
    let best   = ref (abs (getc m.(il) ic)) in
    for j = Stdlib.(il+1) to Stdlib.(nbl - 1) do
      let p = abs (getc m.(j) ic) in
      if p <> zero && (!best = zero || p < !best) then
        (best_j := j; best := p)
    done;
    if !best <> zero then
      begin
        swap_line il !best_j;
        incr i1; incr i2;
        for j = Stdlib.(il+1) to Stdlib.(nbl - 1) do
          let p = getc m.(il) ic in
          let q = getc m.(j) ic in
          if q <> zero then
            begin
              if q mod p <> zero then
                begin
                  let (d,u,v) = gcd p q in
                  let a = p / d in
                  let b = q / d in
                  assert (u * a + v * b = one);
                  comb_line2 il u (-b) j v a;
                  assert (getc m.(j) ic = zero);
                end
              else
                begin
                  assert (q mod p = zero);
                  let x = q / p in
                  comb_line j one il (-x);
                end
            end
        done;
      end
    else (incr i2; incr k)
  done;
  (*printf "end %d %d %d %d %d =>\n%a\n%!" nbl nbc !k !i1 !i2 print_mat m;*)
  Stdlib.(!k + nbc - !i2)

let rank nbl nbc m =
  let k = snf nbl nbc m in
  (*printf "%a\n%!" print_int_matrix m;*)
  Stdlib.(k , nbc - k)
