let _ = Printexc.record_backtrace true


  module Make(R:Field.S) = struct
  open R

  (** vector *)
  type vector = R.t array
  type t = Vector

  (** column matrix *)
  type matrix = vector array

  let ( +++ ) v1 v2 =
    assert (Array.length v1 = Array.length v2);
    Array.mapi (fun i x -> x+.v2.(i)) v1

  let ( ---) v1 v2 =
    assert (Array.length v1 = Array.length v2);
    Array.mapi (fun i x -> x-.v2.(i)) v1

  let comb t v1 u v2 =
    assert (Array.length v1 = Array.length v2);
    Array.mapi (fun i x -> t*.x +. u*.v2.(i)) v1

  let ( *.* ) v1 v2 =
    assert (Array.length v1 = Array.length v2);
    let res = ref zero in
    Array.iteri (fun i x -> res := !res +. x *. v2.(i)) v1;
    !res

  let zero_v d = Array.make d zero

  let ( **.) x v =
    Array.map (fun y -> x*.y) v

  let ( //.) v x = (one /. x) **. v

  let opp v = Array.map (~-.) v

  let dist v1 v2 =
    let x = v1 --- v2 in
    sqrt (x *.* x)

  let dist2 v1 v2 =
    let x = v1 --- v2 in
    x *.* x

  let cos2 v1 v2 =
    let x = v1 *.* v2 in
    (x *. x) /. ((v1 *.* v1) *. (v2 *.* v2))

  let sin2 v1 v2 =
    one -. cos2 v1 v2

  let norm2 v = v *.* v

  let norm v = sqrt (norm2 v)

  let abs_norm v =
    Array.fold_left (fun acc x -> acc +. abs x) zero v

  let normalise v =
    let n = one /. norm v in
    Array.map (fun x -> x *. n) v

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

  let ( *+* ) v m =
    let len = Array.length m in
    let res = Array.make len zero in
    for i = 0 to len - 1 do
      for j = 0 to len -1 do
        res.(j) <- res.(j) +. v.(i) *. m.(i).(j)
      done
    done;
    res

  let ( **** ) m n =
    Array.map (fun v -> m *** v) n

  let swap v i j =
    let tmp = v.(i) in
    v.(i) <- v.(j); v.(j) <- tmp

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
          m.(j) <- comb (-. m.(j).(i)) m.(i) p m.(j);
          d := !d /. p;
        done;
      done;
      for i = 0 to len - 1 do
        d := !d *. m.(i).(i)
      done;
      !d
    with Exit -> zero

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

  let prop v1 v2 =
    let d = Array.length v1 in
    assert (Array.length v2 = d);
    let rec fn l1 l2 i =
      i >= d || (cmp (l1 *. v1.(i)) (l2 *. v2.(i)) = 0 && fn l1 l2 (i+1))
    in
    let rec gn i =
      i >= d || (
        let l2 = v1.(i) and l1 = v2.(i) in
        let b2 = cmp l2 zero = 0 and b1 = cmp l1 zero = 0 in
        b1 = b2 &&
          ((not b1 && fn l1 l2 (i+1)) || (b1 && gn (i+1))))
    in
    gn 0

  let pcoord v m =
    let d = Array.length v in
    assert (Array.length m = d);
    let den = det m in
    if cmp den zero = 0 then raise Not_found;
    Array.init d (fun i ->
        let tmp = m.(i) in
        m.(i) <- v;
        let x = det m /. den in
        m.(i) <- tmp;
        x)

  let bcoord v m =
    let d = Array.length v in
    assert (Array.length m = d+1);
    let best = ref zero in
    let i0 = ref 0 in
    Array.iteri (fun i w -> let d = dist2 v w in
                            if cmp d !best > 0 then (best := d; i0 := i)) m;
    let i0 = !i0 in
    let v = v --- m.(i0) in
    let m = Array.init d (fun i -> let i = if i >= i0 then i+1 else i in
                                   m.(i) --- m.(i0))
    in
    let den = det m in
    if cmp den zero = 0 then raise Not_found;
    let c = Array.init (d+1) (fun i ->
                if i = i0 then zero else
                let i = if i > i0 then i-1 else i in
                let tmp = m.(i) in
                m.(i) <- v;
                let x = det m /. den in
                m.(i) <- tmp;
                x)
    in
    c.(i0) <- Array.fold_left (fun acc x -> acc -. x) one c;
    c

  let transform v m1 m2 =
    let len = Array.length v in
    assert (Array.length m1 = len);
    assert (Array.length m2 = len);
    Array.init len (fun i ->
        let w = try pcoord m2.(i) m1 with Not_found ->
                  Printf.printf "\n%a in %a (det: %a)\n%!" print_vector m2.(i)
                    print_matrix m1 print (det m1);
                  assert false
        in
        let x = ref zero in
        for i = 0 to len - 1 do
          x := !x +. v.(i) *. w.(i);
        done;
        !x)

  (* solves mx = v for m symmetric *)
  let cg m y =
    let d = Array.length y in
    let x = ref (zero_v d) in
    let p = ref (y --- m !x) in
    let r2 = ref (!p *.* !p) in
    let cont = ref true in
    let nb = ref 0 in
    while !cont do
      incr nb;
      let alpha = !r2 /. (!p *.* (m !p)) in
      x := comb one !x alpha !p;
      let r = y --- m !x in
      let r2' = !r2 in
      r2 := r *.* r;
      cont := !nb < 4*d && not (!r2 =. zero) &&
                (!r2 >. epsilon || !r2 <. r2');
      let beta = !r2 /. r2' in
      p := comb one r beta !p;
    done;
    !x

(*
  let m x =  Array.map (Array.map of_int)
            [|[|1;2;3|];
              [|2;4;5|];
              [|3;5;6|] |] *** x
  let y = Array.map of_int [|1;0;1|]
  let e = one /. of_int 1_000_000
  let x = cg e m y
  let r = y --- m x
  let _ = assert (cmp (norm r) e <= 0)


  let m x = Array.map (Array.map of_int)
            [|[|1;2;3;4|];
              [|2;5;6;7|];
              [|3;6;8;9|];
              [|4;7;9;0|]|] *** x
  let y = Array.map of_int [|1;0;-1;1|]
  let e = one /. of_int 1_000_000
  let x = cg e m y
  let r = y --- m x
  let _ = assert (cmp (norm r) e <= 0)
 *)

  exception Found of R.t array

  let zih m0 =
    let nb  = Array.length m0 in
    let dim = Array.length m0.(0) in
    let b = Array.fold_left (---) (zero_v dim) m0 in
    let epsilon = epsilon /. norm b in
    let m = Array.init (dim+1)
              (fun i -> Array.init (nb+1) (fun j ->
                            if i = dim then one else
                              if j = nb then b.(i) else m0.(j).(i)))
    in
    let x = ref (Array.make (nb+1) (one /. of_int (nb+1))) in
    let d1 = Array.init (nb+1) (fun i -> if i = nb then (~-. one) else zero) in
    let cont = ref true in
    try
      while !cont do
        let d y = Array.mapi (fun i y -> y *. !x.(i)) y in
        let m' y = m *** (d y) in
        let mt z = d (m **- z) in
        let mmt z = m' (mt z) in
        let v1 = cg mmt (m' d1) in
        let dir = d1 --- mt v1 in
        let alpha = Array.fold_left (fun acc x -> if x <. acc then x else acc)
                      inf dir
        in
        let old = !x.(nb) in
        x := comb one !x (of_int 9 /. of_int 10 /. abs alpha) (d dir);
        (*Printf.printf "x=%a\n  d=%a\n  test 3: %a\n%!" print_vector !x print_vector (d dir)
          print_vector (m *** !x);*)
        cont := cmp !x.(nb) epsilon > 0;
        if !cont && cmp !x.(nb) old >= 0 then raise (Found v1)
      done;
      true
    with Found v ->
      let v = Array.init dim (fun i -> v.(i)) in
      let r = Array.for_all (fun a -> v *.* a >. zero)  m0 in
      if not r then Printf.printf "\nNOT CONVERGENT\n%!";
      not r


(*
  let a =
    Array.map (Array.map of_int)
      [|
        [|1;0;0|];
        [|1;1;1|];
        [|0;1;0|];
        [|0;0;1|];
        [|-1;2;0|];
        [|2;-1;0|];
        (*        [| -1; -1;0|];*)
        (*        [|0; -1; -1|];*)
      |]

  let x = zih e a
 *)
             (*let _ = Printf.printf "x = %a\n%!" print_vector x*)
end
