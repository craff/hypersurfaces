open FieldGen

module Make(R:SMin) = struct
  include R

  let pow x n =
    let (x,n) = if n < 0 then (one /. x, -n) else (x,n) in
    let rec fn n =
      if n <= 0 then one
      else if n = 1 then x
      else
        let q = fn (n lsr 1) in
        let q2 = q *. q in
        if n land 0x1 = 0 then q2 else q2 *. x
    in
    fn n

  let powf x y = exp (y *. ln x)

  let precision =
    let rec fn n x =
      if one +. x =. one then n
      else fn (n+1) (x /. of_int 2)
    in
    if exact then None else Some (fn 0 one)

  let small p =
    match precision with
    | None -> zero
    | Some n ->
       let e = Stdlib.(int_of_float (ceil (p *. float n) )) in
       one /. pow (of_int 2) e

  type stop_cond =
    { precision : t      (** |x - y| <= value *)
    ; max_steps : int    (** maximum number of steps *)
    }

  let solve_trinome a b c =
    if a =. zero then (-.c /. b, -.c /. b) else
      begin
        let delta = b *. b -. of_int 4 *. a *. c in
        if delta <. zero then raise Not_found;
        if b >. zero then
          ((-. b -. sqrt delta) /. (of_int 2 *. a),
           (of_int 2 *. c) /. (-.b -. sqrt delta))
        else
          ((-. b +. sqrt delta) /. (of_int 2 *. a),
           (of_int 2 *. c) /. (-. b +. sqrt delta))
      end


  let default_stop_cond = { precision = zero
                          ; max_steps = max_int }

  let ball_integrals zero addf f dim nb =
    let nf = of_int nb in
    let s = ref zero in
    let rec fn acc dx r i =
      let nb = to_int (nf *. r +. of_float 0.999999999999) in
      let h = of_int nb in
      if i = 0 then
        for j = -nb+1 to nb do
          let x = (of_int j -. one /. of_int 2) /. h in
          let dx = (dx *. r) /. h in
          let pt = Array.of_list (x *. r :: acc) in
          let fx = f pt in
          s := addf !s dx fx
        done
      else
        for j = -nb+1 to nb do
          let x0 = (of_int j -. one) /. h in
          let x  = (of_int j -. one /. of_int 2) /. h in
          let x1 = (of_int j) /. h in
          let y  = sqrt (one -. x*.x) in
          let dt = abs (x1 -. x0) *. r in
          let acc = (x *. r) :: acc in
          let dx = dx *. dt in
          let r = y *. r in
          fn acc dx r (i-1)
        done
    in
    fn [] one one (dim-1);
    !s

  let ball_integrals1 zero f dim nb =
    let addf v1 x v2 = Array.map2 (fun a b -> a +. x*. b) v1 v2 in
    ball_integrals zero addf f dim nb

  let ball_integrals2 zero f dim nb =
    let addf v1 x v2 = Array.map2 (fun a b -> a +. x*. b) v1 v2 in
    let addm m1 x m2 = Array.map2 (fun a b -> addf a x b) m1 m2 in
    ball_integrals zero addm f dim nb

  let ball_integrals f dim nb =
    let addf v1 x v2 = v1 +. x*.v2 in
    ball_integrals zero addf f dim nb

  let rk4 debug addf addq f t0 t1 x0 nb =
    let h = (t1 -. t0) /. of_int nb in
    let rk4_step t0 x0 =
      let h2 = h /. of_int 2 in
      let k1 = f(t0) (x0) in
      let k2 = f(t0 +. h2) (addf x0 h2 k1) in
      let k3 = f(t0 +. h2) (addf x0 h2 k2) in
      let k4 = f(t0 +. h) (addf x0 h k3) in
      addq x0 (h /. of_int 6) k1;
      addq x0 (h /. of_int 3) k2;
      addq x0 (h /. of_int 3) k3;
      addq x0 (h /. of_int 6) k4;
    in
    let x = Array.copy x0 in
    for i = 0 to nb - 1 do
      let t = t0 +. of_int i *. h in
      debug t x;
      rk4_step t x;
    done;
    debug t1 x;
    x

  let rk4_1 ?(debug=fun _ _ -> ()) f t0 t1 x0 nb =
    let addf v1 x v2 = Array.map2 (fun a b -> a +. x*. b) v1 v2 in
    let addq v1 x v2 = Array.iteri (fun i a -> v1.(i) <- a +. x*. v2.(i)) v1 in
    rk4 debug addf addq f t0 t1 x0 nb


  let rk4_0 ?(debug=fun _ _ -> ()) f t0 t1 x0 nb =
    let addf x1 x x2 = [|x1.(0) +. x*.x2.(0)|] in
    let addq x1 x x2 = x1.(0) <- x1.(0) +. x*.x2.(0) in
    let res = rk4 debug addf addq f t0 t1 [|x0|] nb in
    res.(0)

  let _ =
    let x1 = rk4_0 (fun _ x -> x) zero one one 50 in
    Format.printf "TEST TEST: %a\n%!" print x1;
    let x1 = rk4_1 (fun _ x -> [|x.(1); -.x.(0)|]) zero (of_float (acos 0.0)) [|zero; one|] 50 in
    Format.printf "TEST TEST: %a\n%!" print x1.(0)
  (*
  let _ =
    let f _ = one in
    let x1 = ball_integrals f 1 1000 in
    let x2 = ball_integrals f 2 1000 in
    let x3 = ball_integrals f 3 100 in
    printf "TEST: %a, %a, %a\n%!" print x1 print x2 print x3
      *)

  let digho ?(stop_cond=default_stop_cond) f x y =
    let fx = f x and fy = f y in
    let steps = ref 0 in
    let h = one /. of_int 2 in
    let rec fn x fx y fy =
      incr steps;
      let z = (x +. y) *. h in
      if abs (y -. x) <=. stop_cond.precision
         || !steps >= stop_cond.max_steps then z
      else
        let fz = f z in
        match cmp fz zero with
        | 0 -> z
        | c when c < 0 -> fn z fz y fy
        | _ -> fn x fx z fz
    in
    match cmp fx zero, cmp fy zero with
    | 0, _ -> x
    | _, 0 -> y
    | c1, c2 when c1 < 0 && c2 > 0 -> fn x fx y fy
    | c1, c2 when c1 > 0 && c2 < 0 -> fn y fy x fx
    | _ -> invalid_arg "digho same sign"

  let g = (sqrt (of_int 5) -. one) /. of_int 2

  let secant ?(safe=true) ?(stop_cond=default_stop_cond) f beta0 beta2 =
    let beta0, beta2 =
      if beta2 >. beta0 then (beta0, beta2) else (beta2, beta0)
    in
    let steps = ref 0 in
    let rec fn beta0 f0 beta1 f1 beta2 f2 =
(*      printf "%d: %a %a %a %a %a %a\n%!" !steps print beta0 print f0
        print beta1 print f1
        print beta2 print f2;*)
      if !steps >= stop_cond.max_steps
         || abs ((f0 -. f1) /. f0) <=. stop_cond.precision
         || abs ((f2 -. f1) /. f0) <=. stop_cond.precision
      then beta1 else
        let d1 = (f1 -. f0) /. (beta1 -. beta0) in
        let d2 = (f2 -. f1) /. (beta2 -. beta1) in
        let x = (d1 /. (d1 -. d2)) *. (beta2 -. beta0) +. beta0 in
        let (x,f) =
          if x >. beta0 && x <. beta2 && abs (x -. beta1) >. of_float 1e-4 *. (beta2 -. beta0) then (x, f x)
          else
            let x =
              if beta2 -. beta1 >. beta1 -. beta0 then
                (beta1 +. beta2) /. of_int 2
              else
                (beta0 +. beta1) /. of_int 2
            in
            (x,f x)
        in
        incr steps;
        if x <. beta1 then
          if f <. f1 then
            fn beta0 f0 x f beta1 f1
          else
            fn x f beta1 f1 beta2 f2
        else if f <. f1 then
          fn beta1 f1 x f beta2 f2
        else
          fn beta0 f0 beta1 f1 x f
    in
    let beta1 = (beta0 +. beta2) /. of_int 2 in
    let f0 = f beta0 in
    let f1 = f beta1 in
    let f2 = f beta2 in
    let beta = fn beta0 f0 beta1 f1 beta2 f2 in
    if safe then beta else
      begin
        let f = f beta in
        if f <. f0 && f <. f2 then beta
        else if f0 <. f2 then beta0 else beta1
      end

  let tricho ?(safe=true) ?(stop_cond=default_stop_cond) f beta0 beta3 =
    let steps = ref 0 in
    let rec fn beta0 beta2 f2 beta3 =
      if !steps >= stop_cond.max_steps
         || abs (beta3 -. beta0) <=. stop_cond.precision
      then beta2 else
        begin
          incr steps;
          let beta1 = beta3 -. g *. (beta3 -. beta0) in
          let f1 = f beta1 in
          if f1 <. f2 then fn beta0 beta1 f1 beta2
          else gn beta1 beta2 f2 beta3
        end
    and gn beta0 beta1 f1 beta3 =
      if !steps >= stop_cond.max_steps
         || abs (beta3 -. beta0) <=. stop_cond.precision
      then beta1 else
        begin
          incr steps;
          let beta2 = beta0 +. g *. (beta3 -. beta0) in
          let f2 = f beta2 in
          if f1 <. f2 then fn beta0 beta1 f1 beta2
          else gn beta1 beta2 f2 beta3
        end
    in
    let beta1 = beta3 -. g *. (beta3 -. beta0) in
    let f1 = f beta1 in
    let beta2 = beta0 +. g *. (beta3 -. beta0) in
    let f2 = f beta2 in
    let beta =
      if f1 <. f2 then fn beta0 beta1 f1 beta2
      else if f2 <. f1 then gn beta1 beta2 f2 beta3
      else beta2
    in
    if safe then beta else
      begin
        let f0 = f beta0 in
        let f3 = f beta3 in
        let f = f beta in
        if f <. f0 && f <. f3 then beta
        else if f0 <. f3 then beta0 else beta3
      end

  (* precision *)
  let epsilon = if exact then zero else
                  let rec fn nb x =
                    if (one +. x =. one) then pow (one /. of_int 2) nb
                    else fn (nb + 1) (x /. of_int 2)
                  in
                  let r = fn 0 one in
                  (*Printf.printf "%a\n%!" print r;*)
                  r

  let epsilon2 = epsilon *. epsilon
end
