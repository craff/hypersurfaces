open Args

module Make(R:Field.S) = struct
  open R

  (** vector *)
  type vector = R.t array
  type t = Vector

  (** column matrix *)
  type matrix = vector array

  let ( +++ ) v1 v2 =
    assert (Array.length v1 = Array.length v2);
    Array.mapi (fun i x -> x +. v2.(i)) v1

  let addq v1 v2 = Array.iteri (fun i x -> v1.(i) <- x +. v2.(i)) v1

  let adds v0 v1 v2 = Array.iteri (fun i x -> v0.(i) <- x +. v2.(i)) v1

  let ( --- ) v1 v2 =
    assert (Array.length v1 = Array.length v2);
    Array.mapi (fun i x -> x -. v2.(i)) v1

  let subq v1 v2 = Array.iteri (fun i x -> v1.(i) <- x -. v2.(i)) v1

  let subs v0 v1 v2 = Array.iteri (fun i x -> v0.(i) <- x -. v2.(i)) v1

  let vp v1 v2 =
    assert (Array.length v1 = 3);
    assert (Array.length v2 = 3);
    [| v1.(1) *. v2.(2) -. v1.(2) *. v2.(1)
     ; v1.(2) *. v2.(0) -. v1.(0) *. v2.(2)
     ; v1.(0) *. v2.(1) -. v1.(1) *. v2.(0) |]

  let comb t v1 u v2 =
    assert (Array.length v1 = Array.length v2);
    Array.mapi (fun i x -> t*.x +. u*.v2.(i)) v1

  let combq t v1 u v2 =
    assert (Array.length v1 = Array.length v2);
    Array.iteri (fun i x -> v1.(i) <- t*.x +. u*.v2.(i)) v1

  let combs v0 t v1 u v2 =
    assert (Array.length v1 = Array.length v2);
    Array.iteri (fun i x -> v0.(i) <- t*.x +. u*.v2.(i)) v1

  let ( *.* ) v1 v2 =
    assert (Array.length v1 = Array.length v2);
    let res = ref zero in
    Array.iteri (fun i x -> res := !res +. x *. v2.(i)) v1;
    !res

  let zero_v d = Array.make d zero

  let ( **. ) x v =
    Array.map (fun y -> x*.y) v

  let ( //. ) v x = (one /. x) **. v

  let opp v = Array.map (~-.) v

  let norm2 v = v *.* v

  let norm v = sqrt (norm2 v)

  let dist v1 v2 = norm (v1 --- v2)

  let dist2 v1 v2 = norm2 (v1 --- v2)

  let abs_norm v =
    Array.fold_left (fun acc x -> acc +. abs x) zero v

  let normalise v =
    let n = one /. norm v in
    Array.map (fun x -> x *. n) v

  let normaliseq v =
    let n = one /. norm v in
    Array.iteri (fun i x -> v.(i) <- x *. n) v

  let abs_normalise v =
    let n = one /. abs_norm v in
    Array.map (fun x -> x *. n) v

  let print_array fn ch v =
    Printf.fprintf ch "(";
    Array.iteri (fun i x ->
        if i <> 0 then Printf.fprintf ch ", ";
        fn ch x) v;
    Printf.fprintf ch ")"

  let print_vector = print_array R.print
  let print_matrix = print_array print_vector
  let print_list ch l =
    let pr ch l =
      List.iteri
        (fun i -> Printf.fprintf ch "%s%d" (if i <> 0 then ", " else "")) l
    in
    Printf.fprintf ch "(%a)" pr l

  (** matrix vector multiplication *)
  let ( *** ) m v =
    assert (Array.length v = Array.length (m.(0)));
    Array.map (( *.* ) v) m

  let ( **- ) m v =
    let dim = Array.length v in
    let d2 = Array.length m.(0) in
    assert (dim = Array.length m);
    Array.init d2 (fun i -> let r = ref zero in
                             Array.iteri (fun j x -> r := !r +. m.(j).(i) *. x) v;
                             !r)

  (** transpose matrix vector multiplicaiton *)
  let ( *+* ) v m =
    let len = Array.length m in
    let res = Array.make len zero in
    for i = 0 to len - 1 do
      for j = 0 to len -1 do
        res.(j) <- res.(j) +. v.(i) *. m.(i).(j)
      done
    done;
    res

  (** matrix multiplication *)
  let ( **** ) m n =
    Array.map (fun v -> m *** v) n

  let transpose m =
    let n1 = Array.length m in
    let n2 = Array.length m.(0) in
    Array.init n2 (fun j -> Array.init n1 (fun i -> m.(i).(j)))

  let swap v i j =
    let tmp = v.(i) in
    v.(i) <- v.(j); v.(j) <- tmp

  (** determinant with principal Gauss pivot *)
  let det m =
    let m = Array.map Array.copy m in
    let len = Array.length m in
    let d = ref one in
    try
      for i = 0 to len - 1 do
        let best = ref (abs m.(i).(i)) in
        let best_j = ref i in
        let best_k = ref i in
        for j = i to len - 1 do
          for k = i to len - 1 do
            let a = abs m.(j).(k) in
            if a >. !best then
              begin
                best := a; best_j := j; best_k := k
              end
          done
        done;
        swap m !best_j i;
        if i <> !best_j then d := ~-. !d ;
        for j = 0 to len - 1 do swap m.(j) (!best_k) i; done;
        if i <> !best_k then d := ~-. !d ;
        let p = m.(i).(i) in
        if p =. zero then raise Exit;
        for j = i+1 to len - 1 do
          combq one m.(j) (-. m.(j).(i) /. p) m.(i);
        done;
      done;
      for i = 0 to len - 1 do
        d := !d *. m.(i).(i)
      done;
      !d
    with Exit -> zero

  (** test determinant *)
  let _ =
    let open R in
    assert (cmp (det [| [| one; zero |]; [| zero; one |] |]) one = 0);
    assert (cmp (det [| [| zero; one |]; [| one; zero |] |]) (~-. one) = 0);
    assert (cmp (det [| [| one; one |]; [| one; one |] |]) zero = 0)

  let is_zero m = Array.for_all (fun x -> cmp x zero = 0) m

  let eq m1 m2 =
    try
      Array.iteri (fun i x -> if cmp x m2.(i) <> 0 then raise Exit) m1;
      true
    with
      Exit -> false

  let (//.) x y = if y =. zero then raise Not_found else x /. y

  (* solves m x = y using conjugate gradient,
     for m symmetric positive definite (spd)
     remark: if m is invertible, tm * m is spd *)
  let cg m b =
    let d = Array.length b in
    let x = zero_v d in
    let p = b --- m x in
    let epsilon = epsilon2 *. (b *.* b) in
    let r2 = ref (p *.* p) in
    let prev = ref (x,!r2) in
    let i = ref 0 in
    try
      while true do
        let alpha = !r2 //. (p *.* m p) in
        combq one x alpha p;
        let r = b --- m x in
        let nr2 = r *.* r in
        (*Printf.printf "step: %d, x: %a => %a\n%!" !i print_vector !x print nr2;*)
        let (_,pr2) = !prev in
        if nr2 < pr2 then prev := (x,nr2);
        if nr2 <=. epsilon || !i >= 2*d then raise Exit;
        let beta = nr2 /. !r2 in
        r2 := nr2;
        combq beta p one r;
        incr i;
      done;
      assert false;
    with Exit ->
      let (x,_) = !prev in
      x

  (* solves m x = y for m symmetric positive definite (spd)
     remark: if m is invertible tm * m is spd *)
  let irm_cg m b =
    let d = Array.length b in
    let x = zero_v d in
    let r = b --- m x in
    let r2 = r *.* r in
    let prev = ref (x,r2) in
    try
      if r2 <=. zero then raise Exit;
      let q = r2 //. (r *.* m r) in
      let p = q **. r in
      let beta = m p in
      let i = ref 0 in
      while true do
        addq x p;
        if !i mod d <> 0 then subq r beta else subs r b (m x);
        let nr2 = r *.* r in
(*        if !Args.debug then
          Printf.printf "step: %d, x: %a => %a\n%!" !i print_vector x print nr2;*)
        let (_,pr2) = !prev in
        if nr2 <. pr2 then prev := (x,nr2);
        if nr2 <=. zero || !i >= 2*d then raise Exit;
        let alpha = m r in
        let a11 = r *.* alpha in
        let a12 = p *.* alpha in
        let a22 = p *.* beta  in
        (* (a11 a12      * (a22 -a12 = (det 0
            a12 a22) inv    -a12 a11)   0 det) *)
        let d = a11 *. a22 -. a12 *. a12 in
        if d = zero then raise Exit;
        let a1 = nr2 *. a22 /. d in
        let a2 = nr2 *. (-. a12 /. d) in
        combq a2 p a1 r;
        combq a2 beta a1 alpha;
        incr i
      done;
      assert false;
    with Exit ->
      let (x,_) = !prev in
      x

  let cg = irm_cg

  (** Coordinate *)
  let pcoord v m =
    try
      let tmv = m *** v in
      let tmm x = m *** (m **- x) in
      cg tmm tmv
    with Not_found ->
      assert false

  (** remove one line and column from a matrix *)
  let sub_mat m i0 j0 =
    let n1 = Array.length m in
    let n2 = Array.length m.(0) in
    Array.init (n1 - 1) (fun i ->
        let i = if i >= i0 then i+1 else i in
        Array.init (n2 - 1) (fun j ->
            let j = if j >= j0 then j+1 else j in
            m.(i).(j)))

  let pvec m i =
    let d = Array.length m in
    Array.init d (fun j ->
        let pos = (i + j) mod 2 = 0 in
        let d = det (sub_mat m i j) in
        if pos then d else ~-. d)

  let center m =
    let d = Array.length m in
    let b = Array.make d one in
    m **- cg (fun x -> m *** (m **- x)) b

  let transform v m1 m2 =
    let len = Array.length v in
    assert (Array.length m1 = len);
    assert (Array.length m2 = len);
    Array.init len (fun i ->
        let w = pcoord m2.(i) m1 in
        v *.* w)

      (*
  module Test = struct
  let m x =  Array.map (Array.map of_int)
               [|[|1;2;3|];
                 [|2;4;5|];
                 [|3;5;6|] |] *** x
  let y = Array.map of_int [|1;0;1|]
  let e = one /. of_int 1_000_000
  let x = cg m y
  let x = irm_cg m y
  let r = y --- m x
  let _ = assert (cmp (norm r) e <= 0)


  let m x = Array.map (Array.map of_int)
            [|[|1;2;3;4|];
              [|2;5;6;7|];
              [|3;6;8;9|];
              [|4;7;9;0|]|] *** x
  let y = Array.map of_int [|1;0;-1;1|]
  let e = one /. of_int 1_000_000
  let x = cg m y
  let x = irm_cg m y
  let r = y --- m x
  let _ = assert (cmp (norm r) e <= 0)

  let _ = exit 0
  end
       *)

  exception Found of R.t array

  (* solve m0 x = b with x.(i) >= 0 if pos.(i) *)
  (* a particular case of karmarkar algorithm *)
  let solve_pos a0 b pos =
    let nb  = Array.length a0 in
    let dim = Array.length a0.(0) in
    assert (Array.length b = dim);
    let r = b --- a0 **- (Array.make nb one) in
    let a = Array.init dim
              (fun i -> Array.init (nb+1) (fun j ->
                            if j = nb then r.(i) else a0.(j).(i)))
    in
    let c = Array.init (nb+1) (fun i -> if i = nb then one else zero) in
    let x = Array.make (nb+1) one in
    let cont = ref true in
    try while !cont do
      assert (x.(nb) >. zero);
      let f x = x +. epsilon in
      let d y = Array.mapi (fun i y -> y *. f x.(i)) y in
      let d2 y = Array.mapi (fun i y -> y *. f x.(i) *. f x.(i)) y in
      let p y =
        let z = cg (fun y -> a *** (d2 (a **- y))) (a *** d y) in
        (z, y --- d (a **- z))
      in
      let (z, v) = p (d c) in
      let v = d v in
      let gamma = ref (v.(nb) /. x.(nb)) in
      let gamma_is_last = ref true in
      for i = 0 to nb - 1 do
        let g = v.(i) /. x.(i) in
        if g >. !gamma then (gamma := g; gamma_is_last := false)
      done;
      let gamma = !gamma in
      if gamma <=. zero then
        begin
          (Printf.eprintf "DANGER: gamma: %a, x: %a, v: %a\n%!" print gamma
             print_vector x print_vector v; raise (Found z));
        end;
      let alpha, ncont = if !gamma_is_last then (one, false)
                         else (of_int 9 /. of_int 10, true) in
      cont := ncont;
      let old = x.(nb) in
      combq one x (~-. alpha /. gamma) v;
      if !Args.debug then
        begin
          let r = a *** x in
          Printf.printf "%a %a %a => %a %b\n%!" print_vector x print (alpha/.gamma) print_vector (d v) print_vector r !cont
        end;
      if !cont && x.(nb) >=. old then ((*Printf.printf "found at %a %a %a\n%!" print_vector z print gamma print v.(nb);*) raise (Found z))
        done;
        raise Exit
    with Exit -> Array.sub x 0 nb

  let zih m =
    if Array.exists (fun v -> norm2 v =. zero) m then None else
    let m = Array.map normalise m in
    let nb  = Array.length m in
    let dim = Array.length m.(0) in
    try
      let m = Array.map (fun v -> Array.init (dim+1) (fun i -> if i < dim then v.(i) else one)) m in
      let b = Array.init (dim+1) (fun i -> if i < dim then zero else one) in
      let pos = Array.make nb true in
      ignore (solve_pos m b pos);
      None
    with
      Found(z) ->
       assert (Array.length z = dim + 1);
       let z = Array.sub z 0 dim in
       let v = m *** z in
       if !Args.debug then
         Printf.eprintf "===> %a ===> %a\n%!" print_vector z print_vector v;
       if Array.for_all (fun x -> x <. zero) v then
         Some z
       else
         (if !debug then Printf.printf "REJECT\n%!"; None)

  let a =
    Array.map (Array.map of_int)
      [|
        [|-1;0;0|];
        [|0;-1;0|];
        [|0;0;-1|];
         |]

  let _ = assert (zih a <> None)

  let a =
    Array.map (Array.map of_int)
      [|
        [|1;0;0|];
        [|-1;1;1|];
        [|0;-1;0|];
        [|0;0;-1|];
         |]

  let _ = assert (zih a = None)

end
