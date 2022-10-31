open Printing
open FieldGen
open VectorCommon

(** Functor with linear algebra code for the given field *)
module Make(R:S) = struct

  open R

  (** vector *)
  type t = R.t
  type vector = R.t array
  type v = vector

  (** matrix, line major *)
  type matrix = vector array
  type m = matrix

  (** in place addition *)
  let addq v1 v2 =
    for i = 0 to Array.length v1 - 1 do
      v1.(i) <- v1.(i) +. v2.(i)
    done

  (** set v0 to v1 + v2 *)
  let adds v0 v1 v2 =
    for i = 0 to Array.length v1 - 1 do
      v0.(i) <- v1.(i) +. v2.(i)
    done

  (** addition that allocates a new vector *)
  let ( +++ ) v1 v2 =
    let v = Array.make (Array.length v1) zero in
    adds v v1 v2; v

  (** in place subtraction *)
  let subq v1 v2 =
    for i = 0 to Array.length v1 - 1 do
      v1.(i) <- v1.(i) -. v2.(i)
    done

  (** set v0 to v1 - v2 *)
  let subs v0 v1 v2 =
    for i = 0 to Array.length v1 - 1 do
      v0.(i) <- v1.(i) -. v2.(i)
    done

  (** subtraction that allocates a new vector *)
  let ( --- ) v1 v2 =
    let v = Array.make (Array.length v1) zero in
    subs v v1 v2; v

  (** set v0 to v1 + v2 *)
  let addms m0 m1 m2 =
    let d1 = Array.length m1 in
    let d2 = Array.length m1.(0) in
    for i = 0 to d1 - 1 do
      for j = 0 to d2 - 1 do
      m0.(i).(j) <- m1.(i).(j) +. m2.(i).(j)
      done;
    done

  (** addition that allocates a new matrix *)
  let ( ++++ ) m1 m2 =
    let m = Array.init (Array.length m1)
              (fun _ -> Array.make (Array.length m1.(0)) zero) in
    addms m m1 m2; m

  (** set v0 to v1 + v2 *)
  let subms m0 m1 m2 =
    let d1 = Array.length m1 in
    let d2 = Array.length m1.(0) in
    for i = 0 to d1 - 1 do
      for j = 0 to d2 - 1 do
      m0.(i).(j) <- m1.(i).(j) -. m2.(i).(j)
      done;
    done

  (** addition that allocates a new matrix *)
  let ( ---- ) m1 m2 =
    let m = Array.init (Array.length m1)
              (fun _ -> Array.make (Array.length m1.(0)) zero) in
    subms m m1 m2; m

  (** vector product in dimension 3 only *)
  let vp v1 v2 =
    assert (Array.length v1 = 3);
    assert (Array.length v2 = 3);
    [| v1.(1) *. v2.(2) -. v1.(2) *. v2.(1)
     ; v1.(2) *. v2.(0) -. v1.(0) *. v2.(2)
     ; v1.(0) *. v2.(1) -. v1.(1) *. v2.(0) |]

  (** set v1 to t v1 + u v2*)
  let combq t v1 u v2 =
    for i = 0 to Array.length v1 - 1 do
      v1.(i) <- t*.v1.(i) +. u*.v2.(i)
    done

  (** set v1 to v1 + u v2 *)
  let combqo v1 u v2 =
    for i = 0 to Array.length v1 - 1 do
      v1.(i) <- v1.(i) +. u*.v2.(i)
    done

  (** set v0 to t v1 + u v2 *)
  let combs v0 t v1 u v2 =
    for i = 0 to Array.length v1 - 1 do
      v0.(i) <- t*.v1.(i) +. u*.v2.(i)
    done

  (** allocates a new vector with value t v1 + u v2 *)
  let comb t v1 u v2 =
    let n = Array.length v1 in
    let v = Array.make n zero in
    combs v t v1 u v2; v

  (** set m1 to t m1 + u m2*)
  let mcombq t m1 u m2 =
    for i = 0 to Array.length m1 - 1 do
      for j = 0 to Array.length m2 - 1 do
        m1.(i).(j) <- t*.m1.(i).(j) +. u*.m2.(i).(j)
      done
    done

  (** scalar product *)
  let ( *.* ) v1 v2 =
    let res = ref zero in
    for i = 0 to Array.length v1 - 1 do
      res := !res +. v1.(i) *. v2.(i);
    done;
    !res

  (** allocation of the null vector of dimension d *)
  let zero_v d = Array.make d zero
  let zero_m d1 d2 = Array.init d1 (fun _ -> Array.make d2 zero)

  (** set v to x v *)
  let smulq x v =
    for i = 0 to Array.length v - 1 do
      v.(i) <- x*.v.(i)
    done

  (** set v0 to x v1 *)
  let smuls v0 x v1 =
    for i = 0 to Array.length v1 - 1 do
      v0.(i) <- x*.v1.(i)
    done

  (** alocates a new vector with x v *)
  let ( **. ) x v =
    let n = Array.length v in
    let r = Array.make n zero in
    smuls r x v;
    r

  (** set v0 to x v1 *)
  let smulms m0 x m1 =
    let d1 = Array.length m1 in
    let d2 = Array.length m1.(0) in
    for i = 0 to d1 - 1 do
      for j = 0 to d2 - 1 do
        m0.(i).(j) <- x*.m1.(i).(j)
      done
    done

  (** alocates a new matrix with x m *)
  let ( ***. ) x m =
    let n1 = Array.length m in
    let n2 = Array.length m.(0) in
    let r = zero_m n1 n2 in
    smulms r x m;
    r

  (** division by a scalar *)
  let ( //. ) v x = (one /. x) **. v

  (** opposite *)
  let opp v = (~-.one) **. v

  (** square of the Euclidian norm *)
  let norm2 v = v *.* v

  let fnorm2 m =
    let r = ref zero in
    Array.iter (Array.iter (fun x -> r := !r +. x *. x)) m;
    !r

  (** Euclidian norm *)
  let norm v = sqrt (norm2 v)

  (** Eucidian distance *)
  let dist v1 v2 = norm (v1 --- v2)

  (** Square of Euclidian distance *)
  let dist2 v1 v2 = norm2 (v1 --- v2)

  (** absolute norm *)
  let abs_norm v =
    let r = ref zero in
    for i = 0 to Array.length v - 1 do
      r := !r +. abs v.(i)
    done;
    !r

  (** return the normalisation of v *)
  let normalise v =
    let n = norm v in
    if n =. zero then v else
    (one /. n) **. v

  (** normalise v in place *)
  let normaliseq v =
    let n = norm v in
    assert (n <>. zero);
    smulq (one /. norm v) v

  (** normalisation for absolute norm *)
  let abs_normalise v = (one /. abs_norm v) **. v

  (** printing functions *)
  let print_vector = print_array R.print
  let print_matrix = print_array print_vector

  (** matrix vector multiplication *)
  let ( *** ) m v =
    assert (Array.length v = Array.length (m.(0)));
    Array.map (( *.* ) v) m

  (** transpose matrix vector multiplicaiton *)
  let ( **- ) m v =
    let d1 = Array.length m in
    let d2 = Array.length m.(0) in
    let res = Array.make d2 zero in
    for i = 0 to d1 - 1 do
      for j = 0 to d2 -1 do
        res.(j) <- res.(j) +. v.(i) *. m.(i).(j)
      done
    done;
    res

  (** matrix multiplication *)
  let ( **** ) m n =
    Array.map (fun v -> n **- v) m

  (** transposition **)
  let transpose m =
    let n1 = Array.length m in
    let n2 = Array.length m.(0) in
    Array.init n2 (fun j -> Array.init n1 (fun i -> m.(i).(j)))

  (** swap in a vector *)
  let swap v i j =
    let tmp = v.(i) in
    v.(i) <- v.(j); v.(j) <- tmp

  (** determinant with full principal Gauss pivot.
      the matrice is overwritten *)
  let unsafe_det m =
    let len = Array.length m in
    try
      let d = ref one in
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
          let v = m.(j).(i) in
          m.(j).(i) <- zero;
          for k = i+1 to len - 1 do
            m.(j).(k) <- m.(j).(k) -. v /. p *. m.(i).(k);
          done;
        done;
      done;
      for i = 0 to len - 1 do
        d := !d *. m.(i).(i)
      done;
      !d
    with Exit -> zero

  (** safe determinant that do not touch the matrix *)
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

  (** solve a linear system with Gauss pivot (partial principal for now) *)
  let solve mat vector =
    let dim = Array.length vector in
    assert (dim > 0);
    assert (Array.length mat = dim);
    assert (Array.length mat.(0) = dim);
    let pivot = ref (-1, -1, zero, zero) in
    let update_pivot i j x =
      let a = abs x in
      let (_,_,b,_) = !pivot in
      if a >. b then pivot := (i,j,a,x)
    in
    let get_pivot () =
      let r = !pivot in pivot := (-1,-1,zero,zero); r
    in
    let mat = Array.init dim (fun i ->
                  Array.init dim (fun j ->
                      let x = mat.(i).(j) in
                      update_pivot i j x; x))
    in
    let vector = Array.copy vector in

    let perm = ref [] in
    for i = 0 to dim - 2 do
      (*Printf.printf "%d %a %a\n%!" i print_matrix mat print_vector vector;*)
      let pivot_i, pivot_j, _, pivot_val = get_pivot () in
      (*Printf.printf "pivot: %d %a\n%!" pivot_i print pivot_val;*)
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
      if pivot_j <> i then
        begin
          perm := (i,pivot_j)::!perm;
          for k = 0 to dim - 1 do
            let v = mat.(k).(pivot_j) in
            mat.(k).(pivot_j) <- mat.(k).(i);
            mat.(k).(i) <- v
          done
        end;
      for j = i+1 to dim-1 do
        let v = mat.(j).(i) in
        mat.(j).(i) <- zero;
        for k = i+1 to dim-1 do
          let x = mat.(j).(k) -. v *. mat.(i).(k) /. pivot_val in
          update_pivot j k x;
	  mat.(j).(k) <- x
        done;
        vector.(j) <- vector.(j) -. v *. vector.(i) /. pivot_val
      done;
    done;

    (*Printf.printf "DIAG %a %a\n%!" print_matrix mat print_vector vector;*)

    if mat.(dim-1).(dim-1) =. zero then raise Not_found;
    let r = vector in

    for i = dim - 1 downto 0 do
      for j = i + 1 to dim - 1 do
        r.(i) <- r.(i) -. r.(j) *. mat.(i).(j)
      done;
      assert (mat.(i).(i) <>. zero);
      r.(i) <- r.(i) /. mat.(i).(i)
    done;

    List.iter (fun (j1, j2) ->
        let v = r.(j1) in
        r.(j1) <- r.(j2);
        r.(j2) <- v) !perm;

    (*Printf.printf "FINAL %a %a\n%!" print_matrix mat print_vector r;*)
    r

  let solve_transpose mat0 vector0 =
    let mat = transpose mat0 in
    let vector = Array.copy vector0 in
    solve mat vector

  (** solves m x = y for m symmetric positive definite (spd)
      remark: if m is invertible tm * m is spd. If the matrix is
      not definite, still gives a vector minimizing the error,
      as conjugate gradient is a minimisation procedure.

      This code is a varient of conjugate gradient descibed in
      "Non recursive equivalent of the conjugate gradient method
       without the need to restart" by Josip Dvornik, Damir Lazarevic,
       Antonia Jaguljnjak Lazarevic and Marija Demsic.

      It appears to converge faster and to better solution than
      usual conjugate gradient when the stopping criterion is
      no progress. Still it gives less good solution as Gauss Pivot *)
  let irm_cg ?(epsilon=zero) m b =
    let d = Array.length b in
    (** initial solution *)
    let x = zero_v d in
    (** initial residual and its norm *)
    let r = b --- m x in
    let r2 = r *.* r in
    (** previous solution and residual norm *)
    let prev = ref (x,r2) in
    (** step counter *)
    let i = ref 0 in
    try
      (** exit if residual small enough, by default epsilon=0!*)
      if r2 <=. epsilon then raise Exit;
      (** compute initial beta vector *)
      let q = r2 /. (r *.* m r) in
      let p = q **. r in
      let beta = m p in
      while true do
        (** translate solution *)
        addq x p;
        (** adjust or recompute residual *)
        if !i mod d <> 0 then subq r beta else subs r b (m x);
        let nr2 = r *.* r in
        (** update previous if progress *)
        let (_,pr2) = !prev in
        if nr2 <. pr2 then prev := (x,nr2);
        (** exit if nr2 smaller than epsilon or more than 2d steps,
            normally should converge in d steps, allows for 2d steps
            because of numerical errors *)
        if nr2 <=. epsilon || !i >= 2*d then raise Exit;
        (** solve the 2x2 system for optimizin descent in the
            combined directions *)
        let alpha = m r in
        let a11 = r *.* alpha in
        let a12 = p *.* alpha in
        let a22 = p *.* beta  in
        (* (a11 a12      * (a22 -a12 = (det 0
           a12 a22) inv    -a12 a11)   0 det) *)
        let det = a11 *. a22 -. a12 *. a12 in
        (** exit if det is zero, only append near the solution *)
        if det =. zero then raise Exit;
        (** solution of the 2x2 system *)
        let a1 = nr2 *. a22 /. det in
        let a2 = nr2 *. (-. a12 /. det) in
        (** next descent direction *)
        combq a2 p a1 r;
        (** update beta for next step *)
        combq a2 beta a1 alpha;
        incr i
      done;
      assert false;
    with Exit ->
      let (x,_) = !prev in
      x

  (** using irm_cg as general solver *)

  (** solve m x = y by m tm x' = y with x = tm x' *)
  let solve_cg m a =
    m **- irm_cg (fun x -> m *** (m **- x)) a

  (** solve tm x = y by tm m x' = y with x = tm x' *)
  let solve_transpose_cg m a =
    m *** irm_cg (fun x -> m **- (m *** x)) a

  (** solve m x = y by tm m x = tm y *)
  let solve_cg2 m a =
    irm_cg (fun x -> m *** (m **- x)) (m **- a)

  (** solve tm x = y by m tm x = m y *)
  let solve_transpose_cg2 m a =
    irm_cg (fun x -> m **- (m *** x)) (m *** a)

  (** function comparing the result of two solver for testing purpose *)
  let solve_both_gen ?(tolerance=of_float 1e-6) f1 f2 mul m a =
    let nan = zero /. zero in
    let dim = Array.length a in
    let nf = ref false in
    let s1 = try f1 m a with Not_found -> nf := true; Array.make dim nan in
    let s2 = try f2 m a with Not_found -> nf := true; Array.make dim nan in
    let d = norm2 (s1 --- s2) in
    let r1 = norm2 (mul m s1 --- a) in
    let r2 = norm2 (mul m s2 --- a) in
    if d >. tolerance || r1 >. tolerance || r2 >. tolerance then
      begin
        printf "BAD SOLVE %a %a %a %a (%a %a|%a = %a)\n%!"
          print d print r1 print r2 print (det m)
          print_matrix m print_vector s1 print_vector s2 print_vector a;
        assert false
      end
    else
      printf "%s %a %a\n%!"
        (if r1 =. r2 then "EQ" else if r1 <. r2 then "CG" else "GAUSS")
        print (r2 /. r1) print (r1 /. r2);
    if !nf then raise Not_found else s2

  (** two instances of the previous *)
  let solve_both =
    solve_both_gen solve_cg solve ( *** )

  (** two instances of the previous *)
  let solve_transpose_both =
    solve_both_gen solve_transpose_cg solve_transpose ( **- )

  (** compute the circumcenter of a simplex whose vertices are
      the line of the matrix m and are normalised, in which case
      we must have m.(i) *.* x = one for all i  *)
  let center m =
    let d = Array.length m in
    let b = Array.make d one in
    try solve m b with Not_found -> assert false

  (** same as above when the number of points is lower than the
      dimention of the ambiant space *)
  let lcenter m =
    let d = Array.length m in
    if d = Array.length m.(0) then center m else
      let b = Array.make d one in
      let f v = m *** (m **- v) in
      m **- irm_cg f b

  (** Coordinate: compute the coordinates of v is the basis given
      by the lines of matrix m *)
  let pcoord v m =
    try solve (transpose m) v
    with Not_found -> assert false

  (** Barycentric corrdinates *)
  let bcoord v m =
    let v = Array.append v [|one|] in
    pcoord v m

  (** transform a linear form v given for basis m1 to basis m2 *)
  let transform v m1 m2 =
    m2 *** solve m1 v

  exception Found of R.t array

  (** computes the distance between x and the vector space
      generated by the first k lines of m *)
  let distance m k x =
    let m = Array.init k (fun i -> m.(i)) in
    let mtm v = m *** (m **- v) in
    let y = irm_cg mtm (m *** x) in
    norm2 (x --- m **- y)

  (** Here starts the functions and types related to the zero
      in convex hull test *)


  (** transform r, so that its coefficients sum up to one,
      will be used only with non nul vector with non negative
      coefficients *)
  let set_one r =
    let nb = Array.length r in
    let s = ref zero in
    for j = 0 to nb - 1 do
      s := !s +. r.(j);
    done;
    for j = 0 to nb - 1 do
      r.(j) <- r.(j) /. !s;
    done

  (** Take a vector [v] and a matrix [m] such that [m.(i) *.* v > 0] and
      maximise the min of [m.(i) *.* v] under the constraint [norm2 v = 1].
   *)
  let ameliorate v m =
    ame_log "start ameliorate";
    assert (not (Array.exists (fun v -> norm2 v <=. zero) m));
    let nb = Array.length m in
    let dim = Array.length m.(0) in
    if (nb <= 0) then v else
    let v = normalise v in

    let value v =
      let best = ref inf in
      Array.iter (fun w -> let s = v *.* w in if s <. !best then best := s) m;
      !best
    in

    let direction v goal =
      let values = Array.init nb (fun i -> (m.(i) *.* v, i)) in
      let cmp (x,_) (y,_) = cmp x y in
      Array.sort cmp values;
      let size = ref 1 in
      while !size < dim && !size < nb - 1 &&
              fst values.(!size) <=. goal do incr size done;
      let size = !size in
      ame_log "size: %d dim:%d nb:%d" size dim nb;
      let mm = Array.init (size+1) (fun i ->
                   if i = 0 then v else m.(snd values.(i - 1))) in
      let mm' = transpose mm in
      let b = Array.init (size+1) (fun i ->
                  if i = 0 then zero else (goal -. fst values.(i-1))) in
      ame_log "solving with %a = %a" print_matrix mm print_vector b;
      mm' *** (solve (mm **** mm') b)
    in

    let linear_search v d =
      let fn l =
        let w = normalise (comb one v l d) in
        -. value w
      in
      let stop_cond = { default_stop_cond with max_steps = 15 } in
      tricho ~safe:false ~stop_cond fn zero (of_int 10)
    in

    let rec loop v f step =
      try
        ame_log "loop: %a %a" print f print step;
        let goal = f +. step in
        let d = direction v goal in
        ame_log "d: %a (%a %b)" print_vector d print (norm2 d) (norm2 d <=. zero);
        let l = linear_search v d in
        ame_log "l: %a" print l;
        let step' = step *. l in
        let v' = normalise (comb one v l d) in
        let f' = value v' in
        if f' >. f then loop v' f' step' else v
      with Not_found -> v
    in

    let f0 = value v in
    loop v f0 f0

  (** structure to store statistics about zero in hull test *)
  type zih_steps = {
      mutable nb_call : int;
      mutable nb_abort : int;
      mutable max : int;
      mutable sum : int
    }

  let stop_cond = { precision = zero; max_steps = 50 }

  (** initial stats and reset*)
  let zih_steps = { nb_call = 0; nb_abort = 0; max = 0; sum = 0 }
  let reset_zih () =
    zih_steps.nb_call <- 0;
    zih_steps.nb_abort <- 0;
    zih_steps.max <- 0;
    zih_steps.sum <- 0

  (** print the statistics and reset *)
  let print_zih_stats ff =
    fprintf ff "zih: [nb: %d, avg: %g, max: %d, abort: %d]"
      zih_steps.nb_call
      Stdlib.(float zih_steps.sum /. float zih_steps.nb_call)
      zih_steps.max zih_steps.nb_abort;
    reset_zih ()

  (** exception and function to exit the procedure. the function updates
      the statistics *)
  exception ExitZih of vector option

  let exit_zih ?(abort=false) step r =
    zih_steps.nb_call <- zih_steps.nb_call + 1;
    if abort then zih_steps.nb_abort <- zih_steps.nb_abort + 1
    else if zih_steps.max < step then zih_steps.max <- step;
    zih_steps.sum <- zih_steps.sum + step;
    raise (ExitZih r)

  (** main zero in hull test function, can provide an initial position *)
  let zih ?r0 zlim m0 = try
      (** normalise and transform the list m0 into a matrix *)
      let m0 = List.sort_uniq compare m0 in
      let nb = List.length m0 in
      let m0 = Array.of_list m0 in
      (** if a vector is nul, we exit immediately *)
      if Array.exists (fun v -> norm v <=. zlim) m0 then exit_zih 0 None;
      let m = Array.map normalise m0 in
      zih_log "zih: %a" print_matrix m;
      let dim = Array.length m.(0) in
      (** initial position *)
      let r = match r0 with
        | Some r -> Array.copy r
        | None -> Array.make nb (one /. of_int nb)
      in
      (** in what follows: [v = m **- r] and [v2 = norm2 r] and we are trying to
       have [v2 = 0] with [r]'s coef non negative and summing to one *)
      (** previous descent direction *)
      let pr = Array.make nb zero in

      (** first kind of steps:
          we will update [r] with [r = set_one (r + alpha(delta_i + beta pr))]
          where

          - [pr] is the previous descent direction
            i.e previous [delta_i + beta pr]
          - [delta_i =] vector with one in position such that
                  [m.(i) *.* v <= 0] and minimum

          alpha and beta, will be positive, this will increase all coefficient
          of r keeping r non negative and summing to one thanks to the use of
          set_one. *)
      let conjugate_step step v v2 =
        let candidates = ref [] in
        let nb_c = ref 0 in
        let stop = ref true in
        let sigma = ref zero in
        for j = 0 to nb-1 do
          sigma := !sigma +. pr.(j)
        done;
        let sigma = !sigma in
        for i = 0 to nb - 1 do
          let s = m.(i) *.* v in
          (*zih_log "  %a %a %a" print r.(i) print s print_vector m.(i);*)
          if s <=. zero  then
            begin
              stop := false;
              incr nb_c;
              candidates := i :: !candidates
            end
        done;
        if !stop then
          begin
            zih_log "false";
            let v = ameliorate v m0 in
            let e = if Array.exists (fun w -> v *.* w <. zlim) m0 then None
                    else Some v
            in
            exit_zih step e
          end;
        let i = List.nth !candidates (Random.int !nb_c) in
        (** value of interest, see the article *)
        let p = m **- pr in
        let p2 = norm2 p in
        let pv = p *.* v in
        let w = m.(i) in
        let pw = p *.* w in
        let vw = m.(i) *.* v in
        assert (vw <=. zero || (printf "%d\n%!" i; false) );
        (** function computing [alpha] and [f]: the new [norm v2] from [beta] *)
        let find_alpha beta =
          let w2 = beta *. beta *. p2 +. of_int 2 *. beta *. pw +. one in
          let vw = beta *. pv +. vw in
          let sigma = beta *. sigma +. one in
          let alpha = (v2 *. sigma -. vw) /. (w2 -. vw *. sigma) in
          let f =
            let d = one +. alpha *. sigma in
            (v2 +. of_int 2 *. alpha *. vw +. alpha *. alpha *. w2) /. (d*.d)
          in
          (alpha, f)
        in
        (** computation of best beta by trichotomie *)
        let f beta = snd (find_alpha beta) in
        let beta =
          if pv >. zero then
            begin
              let beta0 = zero in
              let beta1 = -. vw /. pv in
              tricho ~stop_cond f beta0 beta1
            end
          else
            zero
        in
        (** final alpha from best beta *)
        let (alpha, fa) = find_alpha beta in
        (** updating [r], [pr], and computing new [v] and new [v2] ([nv] and
           [nv2]) *)
        for j = 0 to nb - 1 do
          pr.(j) <- pr.(j) *. beta;
        done;
        pr.(i) <- pr.(i) +. one;
        Array.iteri (fun j c -> r.(j) <- r.(j) +. c *. alpha) pr;
        set_one r;
        let nv = m **- r in
        let nv2 = norm2 nv in
        (** [nv2] should be equal (very near with rounding) to [fa], checking
           in log *)
        zih_log "cg step: %d, index: %d, beta: %a, alpha: %a, norm: %a = %a"
          step i print beta print alpha print fa print nv2;
        (nv, nv2)
      in

      (** second kind of steps *)
      let linear_step step v =
        (** we select indices with [r.(i) > 0] *)
        let sel = ref [] in
        for i = 0 to nb - 1 do
          if r.(i) >. zero then sel := i :: !sel;
        done;
        let nsel = Array.of_list !sel in
        let ms = Array.map (fun i -> Array.append (r.(i) **. m.(i)) [|r.(i)|]) nsel in
        let vs = Array.append v [|zero|] in
        (** computing vector s such that [m **- s] is nearest to v
            and sum to zero. We will move [r] is direction [-s] *)
        let s =
          if Array.length nsel > dim then
            let mm v = ms **- (ms *** v) in
            ms *** (irm_cg mm vs)
          else
            let mm v = ms *** (ms **- v) in
            irm_cg mm (ms *** vs)
        in
        let alpha = ref (one) in
        (** we update [r = r + alpha s], computing [alpha] maximum
            to keep r positive. *)
        let cancel = ref (-1) in
        Array.iteri (fun i k ->
            if !alpha *. s.(i) >. one then
              begin
                alpha := one /. s.(i);
                cancel := k
              end) nsel;
        let alpha = !alpha in
        let cancel = !cancel in
        (** if cancel = -1, then alpha = 1 and if [Array.length sel > dim],
            then new v = m **- r will be nul, so we can stop *)
        let r = Array.copy r in
        Array.iteri (fun i k ->
            if k = cancel then (r.(k) <- zero)
            else r.(k) <- r.(k) *. (one -. alpha *. s.(i))) nsel;
        set_one r;
        let nv = m **- r in
        let nv2 = norm2 nv in
        zih_log "lin step: %d, alpha: %a, cancel: %d, sel: %a"
          step print alpha cancel print_int_array nsel;
        (r, cancel, nv, nv2)
      in

      let rec fn step v v2 =
(*        zih_log "step: %d\n\tr: %a\n\tm.v: %a" step
           print_vector r print_vector (m *** v);*)
        let (v,v2) =
          (** one linear step and one conjugate steps. *)
          let (nr, cancel, nv, nv2) = linear_step step v in
          if (nv2 <. v2) then
            begin
              (** pr is set to zero for the cancelled index to force avoid
                  this indice to be updated by the next conjugate step due to
                  the previous descent direction. This appears to be better
                  than resetting pr to zero completely. *)
              if cancel <> -1 then pr.(cancel) <- zero;
              Array.blit nr 0 r 0 nb;
              (nv,nv2)
            end
          else
            begin
              (** linear steps are not always descent steps, so we do not
                  stop if they are rejected *)
              zih_log "reject linear step %a >= %a" print nv2 print v2;
              (v,v2)
            end
        in
        let (v,v2) =
          let (nv,nv2) = conjugate_step step v v2 in
          if (nv2 <. v2) then
            (nv,nv2)
          else
            begin
              (** conjugate steps are always descent step, so failure
                to descent while [m.(i) *.* v] is not always > 0
                means [v] ~ 0 up to numerical errors *)
              zih_log "no progress %a >= %a, stops" print nv2 print v2;
              exit_zih step None;
            end;
        in
        if v2 <. epsilon2 then
          begin
            zih_log "too small %d, stops" step;
            exit_zih step None;
          end;
        (** if too many steps, we stop assuming zero in hull.  *)
        if step > 20 * dim * nb then
          begin
            zih_log "too long %d, stops" step;
            exit_zih ~abort:true step None;
          end;
        fn (step+1) v v2
      in
      (** initial call *)
      let v = m **- r in
      let v2 = norm2 v in
      zih_log "starts";
      fn 0 v v2
    with ExitZih b -> b

  let pih ?r0 zlim x m =
    let m = List.map (fun v -> v --- x) m in
    zih ?r0 zlim m

  (** Quick test for zih*)
  module Test = struct
    let a =
      [ Array.map of_int [|-1;0;0|]
      ; Array.map of_int [|0;-1;0|]
      ; Array.map of_int [|0;0;-1|]
      ]

    let _ = assert (exact || (zih zero a <> None))

    let a =
      [ Array.map of_int [|1;0;0|]
      ; Array.map of_int [|0;-1;0|]
      ; Array.map of_int [|0;0;-1|]
      ; Array.map of_int [|-1;1;1|]
      ]

    let _ = assert (exact || (zih zero a = None))
  end

  (** General equation solver using a mixture of steepest descent and newton
     method *)

  (** solver statistics, can be shared between many solvers, hence are outside
     the functor *)
  type solver_stats =
    { mutable max_reached_steps : int
    ; mutable sum_steps : int
    ; mutable sum_normal : int
    ; mutable nb_calls : int
    ; mutable nb_bad : int
    ; mutable nb_normal : int
    ; mutable nb_abort : int}

  let init_solver_stats () =
    { max_reached_steps = 0
    ; sum_steps = 0
    ; sum_normal = 0
    ; nb_calls = 0
    ; nb_bad = 0
    ; nb_normal = 0
    ; nb_abort = 0 }

  let print_solver_stats ?(name="solver") ff stat =
    let avg =
      if stat.nb_calls > 0 then
        Stdlib.(float stat.sum_steps /. float stat.nb_calls)
      else 0.0
    in
    let avg_normal =
      if stat.nb_normal > 0 then
        Stdlib.(float stat.sum_normal /. float stat.nb_normal)
      else 0.0
    in
    let normal = stat.nb_normal - stat.nb_bad in
    fprintf ff
      "%s: [normal+bad+abort: %d+%d+%d/%d, avg: %.1f, avg_normal: %.1f, max: %d]"
      name normal stat.nb_bad stat.nb_abort stat.nb_calls
      avg avg_normal stat.max_reached_steps

  let reset_solver_stats stat =
    stat.max_reached_steps <- 0;
    stat.sum_steps <- 0;
    stat.sum_normal <- 0;
    stat.nb_calls <- 0;
    stat.nb_normal <- 0;
    stat.nb_bad <- 0;
    stat.nb_abort <- 0

  module type Fun = sig
    val dim : int (** the codomain dimension *)
    val eval : v -> v (** the function to solve *)
    val grad : v -> m (** its gradient, should raise Not_found if null *)
    val final : v -> bool (** a final test to keep point or not *)
    val dist2 : v -> v -> t
    val min_prog_int : int (** limitation of the number of steps, testes every
                               [min_prog_int] steps *)
    val min_prog_coef : t (** should decrease by [min_prog_coef] factor every
                              [min_prof_int] steps *)

    val lambda_min : t (** minimum value for the step size: stop solver if
                          lambda < lamnbda_min *)
    val fun_min : t (** minimum value for the target function.
                        stop solver if a position p with norm2 p < fun_min is reached *)
    val fun_good : t (** When stoping the algorithm, consider that it converges if
                        value is less than fun_good *)

    val stat : solver_stats (** solver stats *)
    val forbidden : (t*v) list ref list
  end

  let project_circle s coef c =
    let c = normalise c in
    let d = c *.* s in
    let s2 = norm2 s in
    if d >. one then
      c
    else
      begin
        let a = sqrt (of_float coef *. (s2 -. one) +. one) in
        assert (s2 >. one);
        assert (s2 -. a*. a >=. zero);
        assert (s2 -. d *. d >. zero);
        let alpha = sqrt ((s2 -. a *. a) /. (s2 -. d *. d)) in
        let beta = (a -. alpha *. d) /. s2 in
        comb alpha c beta s
      end

  (** the main functor *)
  module Solve(F:Fun) = struct

    (** memo of all solutions *)
    let solutions = ref []

    let update_loop_stats normal steps =
      F.stat.nb_calls <- F.stat.nb_calls + 1;
      F.stat.sum_steps <- steps + F.stat.sum_steps;
      if normal then
        begin
          F.stat.nb_normal <- F.stat.nb_normal + 1;
          F.stat.sum_normal <- F.stat.sum_normal + steps;
        end
      else F.stat.nb_abort <- F.stat.nb_abort + 1;
      if steps > F.stat.max_reached_steps then
        F.stat.max_reached_steps <- steps

    (** steepest descent and newton from c *)
    let descent c =
      let r = F.eval c in
      let h = F.grad c in
      let dx = of_int 2 **. (h **- r) in
      let d2 = norm2 dx in
      let r2 = norm2 r in
      (** optimal step:
          f(x + l dx)^2 = f(x)^2 + 2 l f(x) f'(x) dx + ...
                        = r^2 + l d2 + ...
          zero pour l = - d2 /. r2 *)
      let q = -. r2 /. d2 in
      let steepest = (if not (d2 >. zero) then -.one else q) **. dx in
      (** newton direction as usual *)
      let newton = solve h (-. one **. r) in
      (steepest, newton)

    let stop_cond = { default_stop_cond with
                      max_steps = match precision with
                                    None -> 100 | Some n -> n}

    (** [solve rs2 c0] start the solver from [c0]. It reuses an existing
       solution if it reaches a point [x] s.t. [dist2 x s < rs2] for an existing
       solution sd. May raise Not_found is it reached a point of null gradient *)
    let solve project rs2 c0 =
      (** main loop function:
           steps: count the number of steps.
           c: current position
           fc: norm2 c
           nd: newton direction of descent at c
           sd: steepest direction of descent at c
           lambda: coefficient used with both desenct direction *)
      let prev = Previous.create F.min_prog_int in

      let rec loop_eq steps c fc nd sd lambda =
        if not (fc <. inf) then raise Not_found;
        assert (fc >=. zero || (printf "%a %a\n%!" print fc print_vector c; false));
        try (** search for existing solution near enough *)
          if List.exists (fun ptr ->
                 List.exists
                   (fun (_,c') -> F.dist2 c c' <. rs2 || F.dist2 c (opp c') <. rs2)
                   !ptr) F.forbidden
          then raise Not_found;
          let ls =
            List.find_all
              (fun (_,c') -> F.dist2 c c' <. rs2 || F.dist2 c (opp c') <. rs2)
              !solutions
          in
          let (fc',c') = match ls with
            | [] -> raise Exit
            | [(fc',c')] -> (fc',c')
            | (fc',c')::ls ->
               let best_d = ref (min (F.dist2 c c') (F.dist2 c (opp c'))) in
               let best_fc' = ref fc' in
               let best_c' = ref c' in
               List.iter (fun (fc',c') ->
                   let d = dist2 c c' in
                   if d <. !best_d then
                     begin
                       best_d := d;
                       best_fc' := fc';
                       best_c' := c'
                     end) ls;
               (!best_fc',!best_c')
          in
          update_loop_stats false steps;
          let c' = if F.dist2 c c' <. rs2 then c' else opp c' in
          sol_log "abort at step %3d, fc: %a, c: %a"
            steps print fc' print_vector c';
          (fc',c')
        with Exit -> loop steps c fc nd sd lambda
      and loop steps c fc nd sd lambda =
          (* other stopping conditions *)
        let fc1 = try Previous.get prev with Not_found -> inf in
        let q = norm2 nd in
          (*printf "steps: %d %a %a %a %a %a\n%!" steps print fc print fc1 print epsilon2 print (fc1 /. fc) print q;*)
          if lambda <. F.lambda_min || (fc1 <. F.min_prog_coef *. fc)
                                                      || q <. F.fun_min
          then
            begin
              update_loop_stats true steps;
(*                begin
                  printf "BAD at %4d, fc: %a, c: %a, lambda: %a\n%!"
                    steps print fc print_vector c print lambda;
                  printf "\t %a\n%!" print_vector (F.eval c);
                  let m = F.grad c in
                  printf "\t %a (%a)\n%!" print_matrix m print (det m);
                end;*)
              sol_log "ends at %4d, fc: %a, c: %a, lambda: %a"
                steps print fc print_vector c print lambda;
              if not (q <=. F.fun_good) then
                begin
                  F.stat.nb_bad <- F.stat.nb_bad + 1;
                  raise Not_found;
                end;
              if rs2 >. zero then
                begin
                  sol_log "%d solutions" (1 + List.length !solutions);
                  solutions := (fc,c) :: !solutions;
                end;
              (fc,c)
            end
          else
            begin
              (** given [lambda], we search the best [t] by trichotomie
                  for c = c + lambda (t nd + (1 - t) sd)
                high precision is very important here *)
              let f nd t =
                let d = comb t nd (one -. t) sd in
                let c' = project (comb one c lambda d) in
                norm2 (F.eval c')
              in
              let t = tricho ~safe:false ~stop_cond (f nd) zero one in
              (** we compute new position and functional at this position *)
              let d = comb t nd (one -. t) sd in
              let c' = project (comb one c lambda d) in
              (** no move: call loop with negative lambda to stop *)
              if Array.for_all2 (=.) c c' then
                loop steps c fc nd sd (-. one)
              else
              let fc' = norm2 (F.eval c') in
(*            sol_log "%d, c: %a(%a), fc: %a, c': %a(%a), fc': %a(%a), sd: %a (%a), nd! %a,\
                       vc: %a(%a), dc: %a(%a), lambda: %a, beta: %a"
              steps
              print_vector c print (norm2 c) print fc print_vector c' print (norm2 c') print fc' print (fc -. fc')
              print_vector sd print (sd *.* c) print_vector nd
              print_vector (F.eval c') print (F.eval c' *.* c')
              print_matrix (F.grad c') print (det (F.grad c'))
              print lambda print t;*)
              if (is_nan fc && not (is_nan fc')) || fc' <. fc then
                begin
                  (** progress, do to next step, try a bigger lambda *)
                  Previous.add fc' prev;
                  let (sd,nd) = descent c' in
                  loop_eq (steps + 1) c' fc' nd sd one
                end
              else
                (** no progress, try a smaller lambda *)
                loop steps c fc nd sd (lambda /. of_float 1.5)
            end
      in
      (** initial call to the loop *)
      let c0 = try project c0
               with Not_found -> failwith "solve start out of domain"
      in
      let fc0 = norm2 (F.eval c0) in
      sol_log "starting solve at %a => %a" print_vector c0 print fc0;
      Previous.add fc0 prev;
      let (sd,nd) = descent c0 in
      let (_, c as res) = loop_eq 0 c0 fc0 nd sd one in
      if not (F.final c) then raise Not_found else res

  end

  module type FunMin = sig
    val dim : int
    val eval : v -> t
    val grad : v -> v
    val max_steps : int
    val max_proj : int
    val lambda_min : t
    val fun_min : t
    val stat : solver_stats
  end

  module Min(F:FunMin) = struct

    let minimise proj _ c0 =
      let rec fn step lambda c p d m =
        min_log "%d,%a: %a => %a(%a)" step print lambda
          print_vector c print m print_vector d;
        if lambda <. F.lambda_min || step >= F.max_steps then c else
          (try (fun () ->
             let f t =
               let p' = comb t d (one -. t) p in
               let c' = proj (comb one c lambda p') in
               F.eval c'
              in
              let stop_cond = { default_stop_cond with max_steps = 60 } in
              let t = tricho ~safe:false ~stop_cond f zero one in
              (** we compute new position and functional at this position *)
              let p' = comb t d (one -. t) p in
              let c' = proj (comb one c lambda p') in
              let m' = F.eval c' in
              if m' <. m then
                begin
                  let d' = opp (F.grad c') in
                  fn (step+1) (lambda *. of_float 1.3) c' p' d' m'
            end
          else fn step (lambda /. of_int 2) c p d m)
        with Not_found ->
          (fun () -> fn step (lambda /. of_int 2) c p d m)) ()
      in
      min_log "minmax begins";
      let c0 = proj c0 in
      let m0 = F.eval c0 in
      let d0 = opp (F.grad c0) in
      let r = fn 0 m0 c0 d0 d0 m0 in
      min_log "minmax ends";
      r
  end
end

module type V = sig
  type t
  type vector = t array
  type v = vector
  type matrix = vector array
  type m = matrix

  val zero_v : int -> v
  val zero_m : int -> int -> m
  val print_vector : formatter -> vector -> unit
  val print_matrix : formatter -> matrix -> unit

  val norm2   : v -> t
  val fnorm2  : m -> t
  val norm    : v -> t
  val ( *.* ) : v -> v -> t
  val normalise : v -> v
  val normaliseq : v -> unit
  val dist : v -> v -> t
  val dist2 : v -> v -> t
  val distance : m -> int -> v -> t

  val transpose : 'a array array ->'a array array

  val opp : v -> v
  val ( **. ) : t -> v -> v
  val ( //. ) : v -> t -> v
  val ( --- ) : v -> v -> v
  val ( +++ ) : v -> v -> v
  val addq : v -> v -> unit
  val comb : t -> v -> t -> v -> v
  val combq : t -> v -> t -> v -> unit
  val combqo : v -> t -> v -> unit

  val ( ++++ ) : m -> m -> m
  val ( ---- ) : m -> m -> m
  val ( ***. ) : t -> m -> m
  val mcombq : t -> m -> t -> m -> unit

  val det : m -> t
  val ( **** ) : m -> m -> m
  val ( *** ) : m -> v -> v
  val ( **- ) : m -> v -> v

  val center : m -> v
  val lcenter : m -> v
  val pcoord : v -> m -> v
  val bcoord : v -> m -> v
  val transform : v -> m -> m -> v

  val solve : m -> v -> v
  val solve_cg : m -> v -> v

  val zih : ?r0:vector -> t -> vector list -> vector option
  val pih : ?r0:vector -> t -> vector -> vector list -> vector option
  val print_zih_stats : formatter -> unit

  type solver_stats

  val init_solver_stats : unit -> solver_stats
  val print_solver_stats : ?name:string -> formatter -> solver_stats -> unit
  val reset_solver_stats : solver_stats -> unit

  module type Fun = sig
    val dim : int
    val eval : v -> v
    val grad : v -> m
    val final : v -> bool
    val dist2 : v -> v -> t
    val min_prog_int : int
    val min_prog_coef : t
    val lambda_min : t
    val fun_min : t
    val fun_good : t
    val stat : solver_stats
    val forbidden : (t * v) list ref list
  end

  val project_circle : v -> float -> v -> v

  module Solve(_:Fun) : sig
    val solve : (v -> v) -> t -> v -> (t*v)
    val solutions : (t * v) list ref
  end

  module type FunMin = sig
    val dim : int
    val eval : v -> t
    val grad : v -> v
    val max_steps : int
    val max_proj : int
    val lambda_min : t
    val fun_min : t
    val stat : solver_stats
  end

  module Min(_:FunMin) : sig
    val minimise : (v -> v) -> t -> v -> v
  end

end
