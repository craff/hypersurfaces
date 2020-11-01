
module Make(R:Field.S) = struct
  open R

  (** vector *)
  type vector = R.t array
  type t = Vector

  (** column matrix *)
  type matrix = vector array

  let ( +++ ) v1 v2 =
    assert (Array.length v1 = Array.length v2);
    Array.map2 (+.) v1 v2

  let addq v1 v2 = Array.iteri (fun i x -> v1.(i) <- x +. v2.(i)) v1

  let adds v0 v1 v2 = Array.iteri (fun i x -> v0.(i) <- x +. v2.(i)) v1

  let ( --- ) v1 v2 =
    assert (Array.length v1 = Array.length v2);
    Array.map2 (-.) v1 v2

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
    Array.map (fun v -> n **- v) m

  let transpose m =
    let n1 = Array.length m in
    let n2 = Array.length m.(0) in
    Array.init n2 (fun j -> Array.init n1 (fun i -> m.(i).(j)))

  let swap v i j =
    let tmp = v.(i) in
    v.(i) <- v.(j); v.(j) <- tmp

  (** determinant with principal Gauss pivot *)
  let unsafe_det m =
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

  let det m =
    let m = Array.map Array.copy m in
    unsafe_det m

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

  let solve_unsafe mat vector0 =
    let vector = Array.copy vector0 in
    let dim = Array.length vector in

    for i = 0 to dim - 2 do
      (*Printf.printf "%d %a %a\n%!" i print_matrix mat print_vector vector;*)
      let pivot_i, pivot_val =
        let r = ref (-1, zero) in
        for j = i to dim - 1 do
	  let v = mat.(j).(i) in
	  let (_,t) = !r in
	  if abs v > abs t then r := (j, v)
        done;
        !r
      in
      if pivot_i < 0 then raise Not_found;
      if pivot_i <> i then
        begin
          let v = mat.(pivot_i) in
          mat.(pivot_i) <- mat.(i);
          mat.(i) <- v;
          let v = vector.(pivot_i) in
          vector.(pivot_i) <- vector.(i);
          vector.(i) <- v;
        end;
      for j = i+1 to dim-1 do
        let v = mat.(j).(i) in
        mat.(j).(i) <- zero;
        for k = i+1 to dim-1 do
	  mat.(j).(k) <- mat.(j).(k) -. v *. mat.(i).(k) /. pivot_val
        done;
        vector.(j) <- vector.(j) -. v *. vector.(i) /. pivot_val
      done;
    done;

    (*Printf.printf "DIAG %a %a\n%!" print_matrix mat print_vector vector;*)

    let r = vector in

    for i = dim - 1 downto 0 do
      for j = i + 1 to dim - 1 do
        r.(i) <- r.(i) -. r.(j) *. mat.(i).(j)
      done;
      r.(i) <- r.(i) /. mat.(i).(i)
    done;

    (*Printf.printf "FINAL %a %a\n%!" print_matrix mat print_vector r;*)
    r

  let solve mat0 vector0 =
    let mat = Array.map Array.copy mat0 in
    solve_unsafe mat vector0

  let solve_transpose mat0 vector0 =
    let mat = transpose mat0 in
    solve_unsafe mat vector0

   (* solves m x = y for m symmetric positive definite (spd)
      remark: if m is invertible tm * m is spd *)
  let irm_cg m b =
    let d = Array.length b in
    let x = zero_v d in
    let r = b --- m x in
    let r2 = r *.* r in
    let prev = ref (x,r2) in
    let i = ref 0 in
    try
      if r2 <=. zero then raise Exit;
      let q = r2 //. (r *.* m r) in
      let p = q **. r in
      let beta = m p in
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

  let solve_cg m a =
    m **- irm_cg (fun x -> m *** (m **- x)) a

  let solve_transpose_cg m a =
    m *** irm_cg (fun x -> m **- (m *** x)) a

  let solve_cg2 m a =
    irm_cg (fun x -> m *** (m **- x)) (m **- a)

  let solve_transpose_cg2 m a =
    irm_cg (fun x -> m **- (m *** x)) (m *** a)

  let solve_both_gen f1 f2 mul m a =
    let nan = one /. zero in
    let dim = Array.length a in
    let nf = ref false in
    let s1 = try f1 m a with Not_found -> nf := true; Array.make dim nan in
    let s2 = try f2 m a with Not_found -> nf := true; Array.make dim nan in
    let d = norm2 (s1 --- s2) in
    let r1 = norm2 (mul m s1 --- a) in
    let r2 = norm2 (mul m s2 --- a) in
    if d >. of_float 1e-6 || r1 >. of_float 1e-6 || r2 >. of_float 1e-6 then
      begin
        Printf.printf "BAD SOLVE %a %a %a %a (%a %a|%a = %a)\n%!"
          print d print r1 print r2 print (det m)
          print_matrix m print_vector s1 print_vector s2 print_vector a;
        assert false
      end
    else
      Printf.printf "%s %a %a\n%!"
        (if r1 =. r2 then "EQ" else if r1 <. r2 then "CG" else "GAUSS")
        print (r2 /. r1) print (r1 /. r2);
    if !nf then raise Not_found else s2

  let solve_both = solve_both_gen solve_cg solve ( *** )
  let solve_transpose_both = solve_both_gen solve_transpose_cg solve_transpose ( **- )

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
    solve m b

  (** Coordinate *)
  let pcoord v m =
    solve_transpose m v

  let transform v m1 m2 =
    let len = Array.length v in
    assert (Array.length m1 = len);
    assert (Array.length m2 = len);
    Array.init len (fun i ->
        let w = pcoord m2.(i) m1 in
        v *.* w)

  exception Found of R.t array

  let distance m k x =
    let m = Array.init k (fun i -> m.(i)) in
    try norm2 (x --- m **- (solve (m **** transpose m) (m *** x)))
    with Not_found -> zero

  let search_best m f k =
    let nb  = Array.length m in
    let best_i = ref k in
    let best = ref (f m.(k)) in
    for i = k + 1 to nb-1 do
      let x = f m.(i) in
      if x >. !best then (best := x; best_i := i)
    done;
    if !best_i <> k then swap m k !best_i

  let zih_log fmt = Debug.new_debug "zih" 'z' fmt

  let zih m =
    let nb  = Array.length m in
    let dim = Array.length m.(0) in
    if not (Array.for_all (fun x -> norm2 x >. zero) m) then true else
    let m = Array.map normalise m in
    search_best m (fun x -> x.(0)) 0;
    for i = 1 to dim - 1 do
      search_best m (distance m i) i
    done;
    let m = Array.mapi (fun i x -> (x, i)) m in
    let ml = Array.sub m 0 dim in
    let mr = Array.sub m dim (nb - dim) in
    let det m = det (Array.map fst (Array.sub m 0 dim)) in
    let d = det ml in
    assert (d <>. zero);
    if d <. zero then swap ml 0 1;
    let print_point ch (a,i) =
      Printf.fprintf ch "%d:%a" i print_vector a
    in
    let rec print_points ch l =
      match l with
      | [] -> ()
      | [x] -> print_point ch x
      | x::l -> Printf.fprintf ch "%a, %a" print_point x print_points l
    in
    let print_face ch ((a,i),l) =
      let a = Array.to_list a in
      Printf.fprintf ch "%a\\%d\n => [%a]\n" print_points a i print_points l
    in
    let print_faces ch faces =
      List.iteri (fun i face -> Printf.fprintf ch "%d) %a" i print_face face) faces
    in
    let points = Array.to_list mr in
    let visibility x (d,i) =
      let a = Array.init dim (fun j ->
                  if j < i then d.(j)
                  else if j = i then x
                  else d.(j -1)) in
      det a
    in
    let visible x f = visibility x f <. zero in
    let faces =
      List.init dim (fun i ->
          let a =
            Array.init (dim-1) (fun j ->
                if j < i then ml.(j) else ml.(j+1))
          in
          ((a,i),[]))
    in
    let distribute points faces =
      let faces = List.map (fun (f, l) -> (f, ref l)) faces in
      let rec gn points =
        match points with
        | [] -> ()
        | point::points ->
           let best_l = ref None in
           let best_v = ref zero in
           List.iter (fun (face, l) ->
               let v = visibility point face in
               if v <. !best_v then
                 (best_v := v; best_l := Some l)) faces;
           begin
             match !best_l with
             | None -> ()
             | Some l -> l := point :: !l
           end;
           gn points
      in
      gn points;
      List.map (fun (f,l) -> (f, !l)) faces
    in
    let add_one points faces face x =
      let (hole, faces) = List.partition (fun (f,l) -> visible x f) faces in
      (*zih_log "hole for x:%a\n" print_vector (fst x);
        List.iter (fun (f,_) -> zih_log "%a\n%!" print_matrix (tm f)) hole;*)
      if faces = [] then raise Not_found;
      let (hole, remains) = List.split hole in
      let hole = face :: hole in
      let points = List.flatten (points :: remains) in
      let facet (s,k) =
        List.init (dim-1) (fun i ->
            let a =
              Array.init (dim-2) (fun j ->
                  if j < i then s.(j) else s.(j+1))
            in
            let a' = Array.map snd a in
            Array.sort compare a';
            (a', a,i,k))
      in
      let facets = List.flatten (List.map facet hole) in
      zih_log "%d\n%!" (List.length facets);
      let cmp (a,_,_,_) (b,_,_,_) = Stdlib.compare a b in
      let facets = List.sort cmp facets in
      let rec remove_double acc = function
        | [] -> acc
        | (x,_,_,_)::(y,_,_,_)::l when x = y -> remove_double acc l
        | t::l -> remove_double (t::acc) l
      in
      let facets = remove_double [] facets in
      (*zih_log "sorted hole for x:%a\n" print_vector (fst x);
        List.iter (fun (_,f,_,_) -> zih_log "%a\n%!" print_matrix (tm f)) facets;*)
      (*zih_log "%d\n%!" (List.length facets);*)
      let mk_new (_,facet,i,k) =
        let a =
          Array.init (dim-1) (fun j ->
              if j < i then facet.(j)
              else if j = i then x
              else facet.(j-1))
        in
        let d = det (Array.init dim (fun j -> if j < k then a.(j)
                                              else if j = k then ml.(j)
                                              else a.(j-1))) in
        if d <. zero then swap a 0 1;
        zih_log "New face: det:%a, %a" print d print_face ((a,k),[]);
        ((a, k), [])
      in
      let new_faces = List.map mk_new facets in
      zih_log "New faces:\n%a" print_faces new_faces;
      zih_log "Old faces:\n%a" print_faces faces;
      zih_log "Remaining:\n%a" print_points points;
      (points, new_faces @ faces)
    (*zih_log "new faces x:%a\n" print_vector (fst x);
      List.iter (fun (f,_) -> zih_log "%a\n%!" print_matrix (tm f)) news;
      zih_log "old faces x:%a\n" print_vector (fst x);
      List.iter (fun (f,_) -> zih_log "%a\n%!" print_matrix (tm f)) faces;*)
    in
    let rec loop faces =
      let rec fn acc faces =
        match faces with
        | [] -> acc
        | (face,(x::points))::faces ->
           zih_log "Addind point %a to %a"
             print_point x print_face (face,points);
           let (points, faces) = add_one points (acc@faces) face x in
           let faces = distribute points faces in
           zih_log "Loop:\n%a" print_faces faces;
           loop faces
        | (_, [] as face)::faces ->
           fn (face :: acc) faces
      in fn [] faces
    in
  try
    let faces = distribute points faces in
    zih_log "Init faces (%d points):\n %a" (Array.length mr) print_faces faces;
    let faces = loop faces in
    zih_log "Final hull:\n%a" print_faces faces;
    false
  with
    Not_found ->
    zih_log "Zero in hull!";
    assert(
        let indexes = Array.init dim (fun i -> i) in
        Array.for_all (fun i ->
            Array.exists (fun (x,_) -> x.(i) >=. zero) m &&
              Array.exists (fun (x,_) -> x.(i) <=. zero) m) indexes);
    true


(*
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
 *)
end
