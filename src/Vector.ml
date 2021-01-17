open Printing
open FieldGen

(** log for zero in convex hull test *)
let Debug.{ tst = zih_tst; log = zih_log } = Debug.new_debug "hull" 'h'

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
    subs v v1 v2; v[@@inlined always]

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

  (** scalar product *)
  let ( *.* ) v1 v2 =
    let res = ref zero in
    for i = 0 to Array.length v1 - 1 do
      res := !res +. v1.(i) *. v2.(i);
    done;
    !res

  (** allocation of the null vector of dimension d *)
  let zero_v d = Array.make d zero

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
  let normalise v = (one /. norm v) **. v [@@inlined always]

  (** normalise v in place *)
  let normaliseq v = smulq (one /. norm v) v [@@inlined always]

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

   (* solves m x = y for m symmetric positive definite (spd)
      remark: if m is invertible tm * m is spd *)
  let irm_cg ?(epsilon=zero) m b =
    let d = Array.length b in
    let x = zero_v d in
    let r = b --- m x in
    let r2 = r *.* r in
    let prev = ref (x,r2) in
    let i = ref 0 in
    try
      if r2 <=. epsilon then raise Exit;
      let q = r2 /. (r *.* m r) in
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
        if nr2 <=. epsilon || !i >= 2*d then raise Exit;
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
  let pcoord v m = try solve (m **** transpose m)  (m *** v) with Not_found -> assert false

  (* transform a linear application v fomr base m1 to m2 *)
  let transform v m1 m2 =
    m2 *** solve m1 v

  exception Found of R.t array

  let distance m k x =
    let m = Array.init k (fun i -> m.(i)) in
    let mtm = m **** transpose m in
    let mx = m *** x in
    let y = solve mtm mx in
    try norm2 (x --- m **- y)
    with Not_found -> zero

  let print_point ch (a,i) =
    fprintf ch "%d:%a" i print_vector a

  let rec print_points ch l =
    match l with
    | [] -> ()
    | [x] -> print_point ch x
    | x::l -> fprintf ch "%a, %a" print_point x print_points l

  let print_face ch a =
    let a = Array.to_list a in
    fprintf ch "%a\n" print_points a

  let print_faces ch faces =
    List.iteri (fun i face -> fprintf ch "%d) %a" i print_face face) faces

  exception Zih

  let set_one r =
    let nb = Array.length r in
    let s = ref zero in
    for j = 0 to nb - 1 do
      s := !s +. r.(j);
    done;
    for j = 0 to nb - 1 do
      r.(j) <- r.(j) /. !s;
    done

  type zih_steps = {
      mutable nb_call : int;
      mutable nb_abort : int;
      mutable max : int;
      mutable sum : int
    }

  let zih_steps = { nb_call = 0; nb_abort = 0; max = 0; sum = 0 }
  let reset_zih () =
    zih_steps.nb_call <- 0;
    zih_steps.nb_abort <- 0;
    zih_steps.max <- 0;
    zih_steps.sum <- 0

  let print_zih_summary () =
    printf "zih: average steps: %g, max steps: %d, nb_abort: %d\n%!"
      Stdlib.(float zih_steps.sum /. float zih_steps.nb_call)
      zih_steps.max zih_steps.nb_abort;
    reset_zih ()

  exception ExitZih of bool

  let exit_zih ?(abort=false) step r =
    zih_steps.nb_call <- zih_steps.nb_call + 1;
    if abort then zih_steps.nb_abort <- zih_steps.nb_abort + 1
    else if zih_steps.max < step then zih_steps.max <- step;
    zih_steps.sum <- zih_steps.sum + step;
    raise (ExitZih r)

  let zih ?r0 m = try
    let m = List.map normalise m in
    let m = List.sort_uniq compare m in
    let m = Array.of_list m in
    zih_log "zih: %a" print_matrix m;
    let nb  = Array.length m in
    let dim = Array.length m.(0) in
    let r = match r0 with
      | Some r -> Array.copy r
      | None -> Array.make nb (one /. of_int nb)
    in
    let pcoef = Array.make nb zero in
    let last_cancel = ref (-1) in
    let rec fn step v v2 =
      let dir_i = ref (-1) in
      let dir_s = ref zero in
      for i = 0 to nb - 1 do
        let s = m.(i) *.* v in
        if s <=. !dir_s then
          begin
            dir_s := s;
            dir_i := i
          end
      done;
      let i = !dir_i in
      if i < 0 then (zih_log "false"; exit_zih step false);
      let p = m **- pcoef in
      let p2 = norm2 p in
      let pv = p *.* v in
      let pw = p *.* m.(i) in
      let vw = !dir_s in
      let sigma = ref zero in
      for j = 0 to nb-1 do
        sigma := !sigma +. pcoef.(j)
      done;
      let sigma = !sigma in
      let find_alpha beta =
        let w2 = beta *. beta *. p2 +. of_int 2 *. beta *. pw +. one in
        let vw = beta *. pv +. vw in
        let sigma = beta *. sigma +. one in
        let f alpha =
          let d = one +. alpha *. sigma in
          (v2 +. of_int 2 *. alpha *. vw +. alpha *. alpha *. w2) /. (d*.d)
        in
        if vw >=. zero then (zero, f zero) else
          let a = sigma *. (w2 -. vw *. sigma) in
          let b = w2 -. v2 *. sigma *. sigma in
          let c = vw -. sigma *. v2 in
          let alpha1, alpha2 =
            try solve_trinome a b c with Not_found -> assert false
          in
          let f1 = f alpha1 and f2 = f alpha2 in
          if f1 <. f2 then (alpha1, f1) else (alpha2, f2);
      in
      let stop_cond = { default_stop_cond with max_steps = 50 } in
      let f beta = snd (find_alpha beta) in
      let beta =
        if p2 >. zero then
          begin
            let beta0 = zero in
            let beta1 = if pv >. zero then -. vw /. pv else of_int 100 in
            tricho ~stop_cond f beta0 beta1
          end
        else
          zero
      in
      let (alpha, fa) = find_alpha beta in
      for j = 0 to nb - 1 do
        pcoef.(j) <- pcoef.(j) *. beta;
      done;
      pcoef.(i) <- pcoef.(i) +. one;
      Array.iteri (fun j c -> r.(j) <- r.(j) +. c *. alpha) pcoef;
      set_one r;
      let nv = m **- r in
      let nv2 = norm2 nv in
      zih_log "step: %d, index: %d, beta: %a, alpha: %a, norm: %a = %a" step i print beta print alpha print fa print nv2;
      let lin_step () =
        let sel = ref [] in
        for i = 0 to nb - 1 do
          if r.(i) >. zero then sel := i :: !sel;
        done;
        let sel = Array.of_list !sel in
        let ms = Array.map (fun k -> Array.append m.(k) [|one|]) sel in
        let b = Array.append v [|zero|] in
        let (mm,s) =
          if Array.length sel > dim then
            begin
              let mm = transpose ms **** ms in
              let t = solve_cg mm b in
              (mm, ms *** t)
            end
          else
            begin
              let mm = ms **** transpose ms in
              let t = solve_cg mm (ms *** b) in
              (mm, t)
            end
        in
        let alpha = ref one in
        let cancel = ref (-1) in
        Array.iteri (fun i k ->
            if !alpha *. s.(i) >. r.(k) then (alpha := r.(k) /. s.(i); cancel := k)) sel;
        let alpha = !alpha in
        let cancel = !cancel in
        last_cancel := cancel;
        zih_log "lin step step: %d alpha: %a, cancel: %d, det: %a, sel: %a" step print alpha cancel print (det mm) print_int_list (Array.to_list sel);
        let r = Array.copy r in
        Array.iteri (fun i k ->
            if k = cancel then r.(k) <- zero
            else r.(k) <- r.(k) -. alpha *. s.(i)) sel;
        set_one r;
        (r, cancel = -1)
      in
      let nv,nv2 =
        if step mod dim = dim - 1 then (
          let (nr,stop) = lin_step () in
          let nnv = m **- nr in
          let nnv2 = if stop then zero else norm2 nnv in
          let keep = nnv2 <=. nv2 in
          zih_log "linstep norm %a, keep %b" print nnv2 keep;
          if keep then
            begin
              Array.blit nr 0 r 0 nb;
              Array.blit nr 0 pcoef 0 nb; (nnv,nnv2)
            end
          else (nv, nv2)
        ) else (nv,nv2)
      in
      if nv2 >=. v2 then
        begin
          zih_log "no progress %a >= %a" print nv2 print v2;
          exit_zih step true;
        end;
      if step > 100 * nb then
        begin
          zih_log "too long %d" step;
          exit_zih ~abort:true step true;
        end;
      fn (step+1) nv nv2
    in
    let v = m **- r in
    let v2 = norm2 v in
    fn 0 v v2
    with ExitZih b -> b

  type point = R.t array * int
  type faces = point array list

  let pdet (m:point array) = det (Array.map fst m)

  let eqv v w =
    let r = ref true in
    Array.iteri (fun i x -> r := !r && x =. w.(i)) v;
    !r

  let visibility (x:point) (d:point array) =
    (*printf "vis: %d %a\n%!" (Array.length d) print_face d;*)
    try
      let c = center (Array.map fst d) in
      let v = norm2 (c --- fst x) -. norm2 (c --- fst d.(0))  in
      (*printf "vis: %a %a\n%!" print v print_vector c;*)
      v
    with Not_found -> -. inf

  let visible x f = visibility x f <. zero

  let search_best m f k =
    let nb  = Array.length m in
    let best_i = ref k in
    let best = ref (f m.(k)) in
    for i = k + 1 to nb-1 do
      let x = f m.(i) in
      if x >. !best then (best := x; best_i := i)
    done;
    if !best_i <> k then swap m k !best_i

  let reorder dim m =
    search_best m (fun x -> x.(0)) 0;

    for i = 1 to dim - 1 do
      search_best m (distance m i) i
    done

  let delauney m =
    let m = Array.of_list m in
    let nb  = Array.length m in
    let dim = Array.length m.(0) in
    reorder dim m;
    let m = Array.mapi (fun i x -> (x, i)) m in
    let faces = Hashtbl.create 128 in
    let edges = Hashtbl.create 128 in
    let face_key face =
      let k = Array.map snd face in
      Array.sort compare k;
      k
    in
    let edge_key face i =
      let k =
        Array.init (dim - 1) (fun j ->
            if j < i then snd (face.(j)) else snd (face.(j+1)))
      in
      Array.sort compare k;
      k
    in
    let add_edge ml i =
      let key = edge_key ml i in
      let l = try Hashtbl.find edges key with Not_found -> [] in
      Hashtbl.replace edges key ((ml,i)::l)
    in
    let get_face face =
      let key = face_key face in
      try snd (Hashtbl.find faces key) with Not_found -> assert false
    in
    let set_face face points =
      let key = face_key face in
      Hashtbl.replace faces key (face, points)
    in
    let rm_edge ml i =
      let key = edge_key ml i in
      let l = try Hashtbl.find edges key with Not_found -> [] in
      let l = List.filter ((<>) (ml,i)) l in
      if l = [] then Hashtbl.remove edges key else
        Hashtbl.replace edges key l
    in
    let get_edge ml i =
      let key = edge_key ml i in
      let l =  Hashtbl.find edges key in
      match l with
        [x] -> x
      | _ -> assert false
    in
    let add_face face =
      set_face face [];
      for i = 0 to dim - 1 do
        add_edge face i
      done
    in
    let rm_face face =
      let key = face_key face in
      Hashtbl.remove faces key;
      for i = 0 to dim - 1 do
        rm_edge face i
      done
    in
    let distribute points faces =
      List.iter add_face faces;
      let rec gn points =
        match points with
        | [] -> ()
        | point::points ->
           let best_l = ref None in
           let best_v = ref inf  in
           List.iter (fun face ->
               let v = visibility point face in
               if v <. !best_v then
                 (best_v := v; best_l := Some face)) faces;
           begin
             match !best_l with
             | None -> assert false
             | Some face -> set_face face (point :: get_face face)
           end;
           gn points
      in
      gn points;
    in
    let border_tbl = Hashtbl.create 128 in
    let set_border () =
      Hashtbl.clear border_tbl;
      Hashtbl.iter (fun key l ->
          if List.length l = 1 then Hashtbl.add border_tbl key ()) edges;
    in
    let is_border face i =
      Hashtbl.mem border_tbl (edge_key face i)
    in
    let rec add_one border points face x =
      if visible x face then
        begin
          points := List.rev_append (get_face face) !points;
          rm_face face;
          for i = 0 to dim - 1 do
            try
              let (face,_) = get_edge face i in
              add_one border points face x
            with
              Not_found ->
               if is_border face i then
                 begin
                   let a = Array.init dim (fun j -> if i = j then x else face.(j)) in
                   if not (visible face.(i) a) then
                     if List.for_all (fun b -> face_key b <> face_key a) !border
                               then border := a :: !border
                 end
          done;
        end
      else
        begin
          for i = 0 to dim - 1 do
            let a = Array.init dim (fun j -> if i = j then x else face.(j)) in
            if not (visible face.(i) a) then
              if List.for_all (fun b -> face_key b <> face_key a) !border
                   then border := a :: !border
          done
        end
    in

    let rec loop () =
      try
        Hashtbl.iter (fun _ (face, points) ->
          match points with
          | [] -> ()
          | x::points ->
             zih_log "Addind point %a to %a"
               print_point x print_face face;
             set_face face points;
             let points = ref [] in
             let border = ref [] in
             set_border ();
             add_one border points face x;
             assert (!border <> []);
             distribute !points !border;
             raise Exit) faces
      with Exit -> loop ()
    in

    let face = Array.sub m 0 dim in
    let points = Array.to_list (Array.sub m dim (nb - dim)) in
    add_face face;
    set_face face points;
    loop ();

    let res = ref [] in
    Hashtbl.iter (fun _ (face,points) ->
        assert (points = []);
        res := Array.map fst face :: !res) faces;
    !res


  module Test = struct
    let a =
      List.map (Array.map of_int)
        [
          [|-1;0;0|];
           [|0;-1;0|];
           [|0;0;-1|];
           ]

    let _ = assert (exact || not (zih a))

    let a =
      List.map (Array.map of_int)
        [
          [|1;0;0|];
          [|-1;1;1|];
           [|0;-1;0|];
           [|0;0;-1|];
           ]

    let _ = assert (exact || zih a)

  end
end

module type V = sig
  type t
  type vector = t array
  type v = vector
  type matrix = vector array
  type m = matrix

  val zero_v : int -> v
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

  val det : m -> t
  val ( **** ) : m -> m -> m
  val ( *** ) : m -> v -> v
  val ( **- ) : m -> v -> v

  val center : m -> v
  val pcoord : v -> m -> v
  val transform : v -> m -> m -> v

  val solve : m -> v -> v
  val solve_cg : m -> v -> v

  type point = t array * int
  type faces = point array list
  exception Zih
  val reorder : int -> m -> unit
  val delauney : v list -> m list
  val visibility : point -> point array -> t

  val zih : ?r0:vector -> vector list -> bool
  val print_zih_summary : unit -> unit
end
