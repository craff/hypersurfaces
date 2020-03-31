module Make(R:Field.S) = struct
  open R

  (** vector *)
  type vector = t array

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

  let dist v1 v2 =
    let x = v1 --- v2 in
    sqrt (to_float (x *.* x))

  let dist2 v1 v2 =
    let x = v1 --- v2 in
    x *.* x

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
    Array.map (( *.* ) v) m

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
            if abs m.(j).(k) > !best then
              begin
                best := abs m.(j).(k); best_j := j; best_k := k
              end
          done
        done;
        swap m !best_j i;
        if i <> !best_j then d := ~-. !d ;
        for j = 0 to len - 1 do swap m.(j) (!best_k) i; done;
        if i <> !best_k then d := ~-. !d ;
        let p = m.(i).(i) in
        if cmp p zero = 0 then raise Exit;
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
                            if d > !best then (best := d; i0 := i)) m;
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
                  Printf.printf "%a in %a\n%!" print_vector m2.(i)
                    print_matrix m1;
                  assert false
        in
        let x = ref zero in
        for i = 0 to len - 1 do
          x := !x +. v.(i) *. w.(i);
        done;
        !x)

end
