open Printing
open FieldGen

(** log for zero in convex hull test *)
let Debug.{ log = zih_log } = Debug.new_debug "hull" 'h'
let Debug.{ log = tri_log } = Debug.new_debug "triangulation" 'z'
let Debug.{ log = sol_log } = Debug.new_debug "solve" 's'

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
    done;
    [@@inlined always]

  (** set v0 to v1 + v2 *)
  let adds v0 v1 v2 =
    for i = 0 to Array.length v1 - 1 do
      v0.(i) <- v1.(i) +. v2.(i)
    done;
    [@@inlined always]

  (** addition that allocates a new vector *)
  let ( +++ ) v1 v2 =
    let v = Array.make (Array.length v1) zero in
    adds v v1 v2; v[@@inlined always]

  (** in place subtraction *)
  let subq v1 v2 =
    for i = 0 to Array.length v1 - 1 do
      v1.(i) <- v1.(i) -. v2.(i)
    done;
    [@@inlined always]

  (** set v0 to v1 - v2 *)
  let subs v0 v1 v2 =
    for i = 0 to Array.length v1 - 1 do
      v0.(i) <- v1.(i) -. v2.(i)
    done;
    [@@inlined always]

  (** subtraction that allocates a new vector *)
  let ( --- ) v1 v2 =
    let v = Array.make (Array.length v1) zero in
    subs v v1 v2; v [@@inlined always]

  (** set v0 to v1 + v2 *)
  let addms m0 m1 m2 =
    let d1 = Array.length m1 in
    let d2 = Array.length m1.(0) in
    for i = 0 to d1 - 1 do
      for j = 0 to d2 - 1 do
      m0.(i).(j) <- m1.(i).(j) +. m2.(i).(j)
      done;
    done;
    [@@inlined always]

  (** addition that allocates a new matrix *)
  let ( ++++ ) m1 m2 =
    let m = Array.init (Array.length m1)
              (fun _ -> Array.make (Array.length m1.(0)) zero) in
    addms m m1 m2; m [@@inlined always]

  (** set v0 to v1 + v2 *)
  let subms m0 m1 m2 =
    let d1 = Array.length m1 in
    let d2 = Array.length m1.(0) in
    for i = 0 to d1 - 1 do
      for j = 0 to d2 - 1 do
      m0.(i).(j) <- m1.(i).(j) -. m2.(i).(j)
      done;
    done;
    [@@inlined always]

  (** addition that allocates a new matrix *)
  let ( ---- ) m1 m2 =
    let m = Array.init (Array.length m1)
              (fun _ -> Array.make (Array.length m1.(0)) zero) in
    subms m m1 m2; m [@@inlined always]

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
    done [@@inlined always]

  (** set v1 to v1 + u v2 *)
  let combqo v1 u v2 =
    for i = 0 to Array.length v1 - 1 do
      v1.(i) <- v1.(i) +. u*.v2.(i)
    done [@@inlined always]

  (** set v0 to t v1 + u v2 *)
  let combs v0 t v1 u v2 =
    for i = 0 to Array.length v1 - 1 do
      v0.(i) <- t*.v1.(i) +. u*.v2.(i)
    done [@@inlined always]

  (** allocates a new vector with value t v1 + u v2 *)
  let comb t v1 u v2 =
    let n = Array.length v1 in
    let v = Array.make n zero in
    combs v t v1 u v2; v [@@inlined always]

  (** set m1 to t m1 + u m2*)
  let mcombq t m1 u m2 =
    for i = 0 to Array.length m1 - 1 do
      for j = 0 to Array.length m2 - 1 do
        m1.(i).(j) <- t*.m1.(i).(j) +. u*.m2.(i).(j)
      done
    done [@@inlined always]

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
    done [@@inlined always]

  (** set v0 to x v1 *)
  let smuls v0 x v1 =
    for i = 0 to Array.length v1 - 1 do
      v0.(i) <- x*.v1.(i)
    done [@@inlined always]

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
    done [@@inlined always]

  (** alocates a new vector with x v *)
  let ( ***. ) x v =
    let n1 = Array.length v in
    let n2 = Array.length v.(0) in
    let r = zero_m n1 n2 in
    smulms r x v;
    r

  (** division by a scalar *)
  let ( //. ) v x = (one /. x) **. v [@@inlined always]

  (** opposite *)
  let opp v = (~-.one) **. v [@@inlined always]

  (** square of the Euclidian norm *)
  let norm2 v = v *.* v [@@inlined always]

  (** Euclidian norm *)
  let norm v = sqrt (norm2 v) [@@inlined always]

  (** Eucidian distance *)
  let dist v1 v2 = norm (v1 --- v2) [@@inlined always]

  (** Square of Euclidian distance *)
  let dist2 v1 v2 = norm2 (v1 --- v2) [@@inlined always]

  (** absolute norm *)
  let abs_norm v =
    let r = ref zero in
    for i = 0 to Array.length v - 1 do
      r := !r +. abs v.(i)
    done;
    !r [@@inlined always]

  (** return the normalisation of v *)
  let normalise v =
    let n = norm v in
    if n =. zero then v else
    (one /. n) **. v [@@inlined always]

  (** normalise v in place *)
  let normaliseq v =
    let n = norm v in
    assert (n <>. zero);
    smulq (one /. norm v) v [@@inlined always]

  (** normalisation for absolute norm *)
  let abs_normalise v = (one /. abs_norm v) **. v [@@inlined always]

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
    v.(i) <- v.(j); v.(j) <- tmp [@@inlined always]

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
  let solve_unsafe mat vector =
    let dim = Array.length vector in

    for i = 0 to dim - 2 do
      (*Printf.printf "%d %a %a\n%!" i print_matrix mat print_vector vector;*)
      let pivot_i, _, pivot_val =
        let r = ref (-1, zero, zero) in
        for j = i to dim - 1 do
	  let v = mat.(j).(i) in
          let av = abs v in
          let (_,aw,_) = !r in
	  if av >. aw then r := (j, av, v)
        done;
        !r
      in
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

    if mat.(dim-1).(dim-1) =. zero then raise Not_found;
    let r = vector in

    for i = dim - 1 downto 0 do
      for j = i + 1 to dim - 1 do
        r.(i) <- r.(i) -. r.(j) *. mat.(i).(j)
      done;
      assert (mat.(i).(i) <>. zero);
      r.(i) <- r.(i) /. mat.(i).(i)
    done;

    (*Printf.printf "FINAL %a %a\n%!" print_matrix mat print_vector r;*)
    r

  let solve mat0 vector0 =
    let mat = Array.map Array.copy mat0 in
    let vector = Array.copy vector0 in
    solve_unsafe mat vector

  let solve_transpose mat0 vector0 =
    let mat = transpose mat0 in
    let vector = Array.copy vector0 in
    solve_unsafe mat vector

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
        if det = zero then raise Exit;
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

  (** compute the gravity center of a simplex whose vertices are
      the line of the matrix m and are normalise, in which case
      we must have m.(i) *.* x = one for all i  *)
  let center m =
    let d = Array.length m in
    let b = Array.make d one in
    solve m b

  (** Coordinate: compute the coordinates of v is the basis given
      by the lines of matrix m *)
  let pcoord v m =
    try solve (transpose m) v
    with Not_found -> assert false

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

  (** structure to store statistics about zero in hull test *)
  type zih_steps = {
      mutable nb_call : int;
      mutable nb_abort : int;
      mutable max : int;
      mutable sum : int
    }

  (** initial stats and reset*)
  let zih_steps = { nb_call = 0; nb_abort = 0; max = 0; sum = 0 }
  let reset_zih () =
    zih_steps.nb_call <- 0;
    zih_steps.nb_abort <- 0;
    zih_steps.max <- 0;
    zih_steps.sum <- 0

  (** print the statistics and reset *)
  let print_zih_stats ff =
    fprintf ff "zih: [avg: %g, max: %d, abort: %d]"
      Stdlib.(float zih_steps.sum /. float zih_steps.nb_call)
      zih_steps.max zih_steps.nb_abort;
    reset_zih ()

  (** exception and function to exit the procedure. the function updates
      the statistics *)
  exception ExitZih of bool

  let exit_zih ?(abort=false) step r =
    zih_steps.nb_call <- zih_steps.nb_call + 1;
    if abort then zih_steps.nb_abort <- zih_steps.nb_abort + 1
    else if zih_steps.max < step then zih_steps.max <- step;
    zih_steps.sum <- zih_steps.sum + step;
    raise (ExitZih r)

  (** main zero in hull test function, can provide an initial position *)
  let zih ?r0 m0 = try
      (** normalise and transform the list m0 into a matrix *)
      let m0 = List.sort_uniq compare m0 in
      let nb = List.length m0 in
      let m = Array.make nb [||] in
      List.iteri (fun i v -> m.(i) <- normalise v) m0;
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
      (** there appears to be very rare cycle slowing down convergence where
          the value cancelled by a linear step become again positive in the
          next dim conjugate steps, and is recancelled again, preventing other
          indices to be cancelled. So we remember the last indice cancelled
          by a linear step to avoid that cycle. *)
      let last_cancel = ref (-1) in

      (** first kind of steps *)
      let conjugate_step step v v2 =
        let dir_i = ref (-1) in
        let dir_s = ref zero in
        (** we will update [r] with [r = set_one (r + alpha(delta_i + beta pr))]
           where

           - [pr] is the previous descent direction
                  i.e previous [delta_i + beta pr]
           - [delta_i =] vector with one in position such that
                  [m.(i) *.* v <= 0] and minimum

           alpha and beta, will be positive, this will increase all coefficient
           of r keeping r non negative and summing to one thanks to the use of
           set_one.
          *)
        for i = 0 to nb - 1 do
          let s = m.(i) *.* v in
          if s <=. !dir_s && i <> !last_cancel then
            begin
              dir_s := s;
              dir_i := i
            end
        done;
        let i = !dir_i in
        if i < 0 then (zih_log "false"; exit_zih step false);
        (** value of interest, see the article *)
        let p = m **- pr in
        let p2 = norm2 p in
        let pv = p *.* v in
        let w = m.(i) in
        let pw = p *.* w in
        let vw = !dir_s in
        let sigma = ref zero in
        for j = 0 to nb-1 do
          sigma := !sigma +. pr.(j)
        done;
        let sigma = !sigma in
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
        let stop_cond = { default_stop_cond with max_steps = 50 } in
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
      let linear_step step v _v2 =
        (** we select indices with [r.(i) > 0] *)
        let sel = ref [] in
        for i = 0 to nb - 1 do
          if r.(i) >. zero then sel := i :: !sel;
        done;
        let sel = Array.of_list !sel in
        (** matrix, adding one to have the linear constraint that coefficient
           sum to zero *)
        let ms = Array.map (fun k -> Array.append m.(k) [|one|]) sel in
        let b = Array.append v [|zero|] in
        (** computing vector s such that [m **- s] is nearest to v
            and sum to zero. We will move [r] is direction [-s] *)
        let s =
          (** the system to solve depend upon the size of the selection *)
          if Array.length sel > dim then
            begin
              let mm v = ms **- (ms *** v) in
              let t = irm_cg mm b in
              ms *** t
            end
          else
            begin
              let mm v = ms *** (ms **- v) in
              let t = irm_cg mm (ms *** b) in
              t
            end
        in
        (** we update [r = r - alpha s], computing [alpha <= 1] maximum
            to keep r positive. *)
        let alpha = ref one in
        let cancel = ref (-1) in
        Array.iteri (fun i k ->
            if !alpha *. s.(i) >. r.(k) then
              begin
                alpha := r.(k) /. s.(i);
                cancel := k
              end) sel;
        let alpha = !alpha in
        let cancel = !cancel in
        (** if cancel = -1, then alpha = 1 and if [Array.length sel > dim],
            then new v = m **- r will be nul, so we can stop *)
        let r = Array.copy r in
        Array.iteri (fun i k ->
            if k = cancel then (r.(k) <- zero)
            else r.(k) <- r.(k) -. alpha *. s.(i)) sel;
        let nv = m **- r in
        let nv2 = norm2 nv in
        zih_log "lin step: %d, alpha: %a, cancel: %d, sel: %a, norm = %a"
          step print alpha cancel print_int_list (Array.to_list sel) print nv2;
        (r, cancel, nv, nv2)
      in

      let rec fn step v v2 =
        zih_log "starts";
        let (v,v2) =
          (** one linear step for dim conjugate steps. *)
          if step mod (dim + 1) = 0 then
            let (nr, cancel, nv, nv2) = linear_step step v v2 in
            if (nv2 <. v2) then
              begin
                (** pr is set to zero for the cancelled index to force avoid
                    this indice to be updated by the next conjugate step due to
                    the previous descent direction. This appears to be better
                    than resetting pr to zero completely. *)
                if cancel <> -1 then pr.(cancel) <- zero;
                last_cancel := cancel;
                Array.blit nr 0 r 0 nb;
                (nv,nv2)
              end
            else
              begin
                last_cancel := -1;
                (** linear steps are not always descent steps, so we do not
                   stop if the are rejected *)
                zih_log "reject linear step %a >= %a" print nv2 print v2;
                (v,v2)
              end
          else
            let (nv,nv2) = conjugate_step step v v2 in
            if (nv2 <. v2) then
              (nv,nv2)
            else
              begin
                (** conjugate steps are always descent step, so failure
                    to descent while [m.(i) *.* v] is not always > 0
                    means [v] ~ 0 up to numerical errors *)
                zih_log "no progress %a >= %a, stops" print nv2 print v2;
                exit_zih step true;
              end;
        in
        (** it too many steps, we stop assuming zero in hull, currently do not
           appends on examples. *)
        if step > 20 * dim * nb then
          begin
            zih_log "too long %d, stops" step;
            exit_zih ~abort:true step true;
          end;
        fn (step+1) v v2
      in
      (** initial call *)
      let v = m **- r in
      let v2 = norm2 v in
      fn 0 v v2
    with ExitZih b -> b

  let pih ?r0 x m =
    let m = List.map (fun v -> v --- x) m in
    zih ?r0 m

  (** Quick test for zih*)
  module Test = struct
    let a =
      [ Array.map of_int [|-1;0;0|]
      ; Array.map of_int [|0;-1;0|]
      ; Array.map of_int [|0;0;-1|]
      ]

    let _ = assert (exact || not (zih a))

    let a =
      [ Array.map of_int [|1;0;0|]
      ; Array.map of_int [|0;-1;0|]
      ; Array.map of_int [|0;0;-1|]
      ; Array.map of_int [|-1;1;1|]
      ]

    let _ = assert (exact || zih a)
  end

  (** General equation solver using a mixture of steepest descent and newton
     method *)

  (** solver statistics, can be shared between many solvers, hence are outside
     the functor *)
  type solver_stats =
    { mutable max_reached_steps : int
    ; mutable sum_steps : int
    ; mutable nb_calls : int }

  let init_solver_stats () =
    { max_reached_steps = 0
    ; sum_steps = 0
    ; nb_calls = 0 }

  let print_solver_stats ff stat =
    let avg =
      if stat.nb_calls > 0 then
        Stdlib.(float stat.sum_steps /. float stat.nb_calls)
      else 0.0
    in
    fprintf ff
      "solver: [nb: %d, avg: %.1f, max: %d]"
        stat.nb_calls avg stat.max_reached_steps

  let reset_solver_stats stat =
    stat.max_reached_steps <- 0;
    stat.sum_steps <- 0;
    stat.nb_calls <- 0

  module type Fun = sig
    val dim : int (** the codomain dimension *)
    val eval : v -> v (** the function to solve *)
    val grad : v -> m (** its gradient, should raise Not_found if
                          null *)
    val max_steps : int (** limitation of the number of steps *)
    val stat : solver_stats (** solver stats *)
  end

  (** the main functor *)
  module Solve(F:Fun) = struct

    (** memo of all solutions *)
    let solutions = ref []

    let update_loop_stats steps =
      F.stat.nb_calls <- F.stat.nb_calls + 1;
      F.stat.sum_steps <- steps + F.stat.sum_steps;
      if steps > F.stat.max_reached_steps then
        F.stat.max_reached_steps <- steps

    (** steepest descent and newton from c *)
    let descent c =
      let r = F.eval c in
      let h = F.grad c in
      let dx = h *** r in
      let d2 = norm2 dx in
      if d2 <=. zero then raise Not_found;
      (** optimal step should be
          (-. (r *.* dx) /. d2) **. dx
          but the following is much better ... do not know why *)
      let steepest = (-. norm2 r /. d2) **. dx in
      (** newton direction as usual *)
      let newton =
        try solve h (-. one **. r)
        with Not_found -> zero_v F.dim
      in
      (steepest, newton)

    (** [solve rs2 c0] start the solver from [c0]. It reuses an existing
       solution if it reaches a point [x] s.t. [dist2 x s < rs2] for an existing
       solution s. May raise Not_found is it reached a point of null gradient *)
    let solve rs2 c0 =
      (** main loop function:
           steps: count the number of steps.
           c: current position
           fc: norm2 c
           nd: newton direction of descent at c
           sd: steepest direction of descent at c
           lambda: coefficient used with both desenct direction *)

      let rec loop steps c fc nd sd lambda =
        assert (fc >=. zero);
        try (** search for existing solution near enough *)
          let (c',f') =
            List.find (fun (c',_) -> dist2 c c' < rs2) !solutions
          in
          update_loop_stats steps;
          sol_log "abort at step %d, c: %a, fc: %a"
            steps print_vector c' print f';
          (c',f',steps)
        with Not_found -> (* other stopping conditions *)
          if lambda <. epsilon2 || fc <. epsilon2 || steps > F.max_steps then
            begin
              update_loop_stats steps;
              sol_log "%d, c: %a, fc: %a"
                steps print_vector c print fc;
              if steps < F.max_steps then
                begin
                  sol_log "%d solutions" (1 + List.length !solutions);
                  solutions := (c,fc) :: !solutions;
                end;
              (c,fc,steps)
            end
          else
            begin
              (** given [lambda], we search the best [t] by trichotomie
                for c = c + lambda (t nd + (1 - t) sd)
                high precision is very important here *)
              let f t =
                let d = comb t nd (one -. t) sd in
                let c0' = comb one c lambda d in
                let c' = normalise c0' in
                norm2 (F.eval c')
              in
              let stop_cond = { default_stop_cond with max_steps = 60 } in
              let t = tricho ~safe:false ~stop_cond f zero one in
              (** we compute new position and functional at this position *)
              let d = comb t nd (one -. t) sd in
              let c0' = comb one c lambda d in
              let c' = normalise c0' in
              let fc' = norm2 (F.eval c') in
              (*
              sol_log "%d, c: %a, fc: %a, c': %a, fc': %a(%a), lambda: %a, beta: %a, rmax - sin: %a"
              steps
              print_vector c print fc print_vector c' print fc' print (fc -. fc')
              print lambda print t print (rmax2 -. sin2 c);*)
              if fc' <. fc then
                begin
                  (** progress, do to next step, try a bigger lambda *)
                  let (sd,nd) = descent c' in
                  loop (steps + 1) c' fc' nd sd (min one (lambda *. of_int 11))
                end
              else
                (** no progress, try a smaller lambda *)
                loop steps c fc nd sd (lambda /. of_int 2)

            end
      in
      (** initial call to the loop *)
      let fc0 = norm2 (F.eval c0) in
      let (sd,nd) = descent c0 in
      let (c1,fc1,_) = loop 0 c0 fc0 nd sd one in
      (c1, fc1)

  end [@@inlined always]

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
  val norm    : v -> t
  val ( *.* ) : v -> v -> t
  val normalise : v -> v
  val dist2 : v -> v -> t

  val transpose : 'a array array ->'a array array

  val opp : v -> v
  val ( **. ) : t -> v -> v
  val ( //. ) : v -> t -> v
  val ( --- ) : v -> v -> v
  val ( +++ ) : v -> v -> v
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
  val pcoord : v -> m -> v
  val transform : v -> m -> m -> v

  val solve : m -> v -> v
  val solve_cg : m -> v -> v

  val zih : ?r0:vector -> vector list -> bool
  val pih : ?r0:vector -> vector -> vector list -> bool
  val print_zih_stats : formatter -> unit

  type solver_stats

  val init_solver_stats : unit -> solver_stats
  val print_solver_stats : formatter -> solver_stats -> unit
  val reset_solver_stats : solver_stats -> unit

  module type Fun = sig
    val dim : int
    val eval : v -> v
    val grad : v -> m
    val max_steps : int
    val stat : solver_stats
  end

  module Solve(F:Fun) : sig
    val solve : t -> v -> (v * t)
  end

end
