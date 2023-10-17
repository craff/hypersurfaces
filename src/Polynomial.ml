open Printing
open FieldGen

module Make(R:S) (V:Vector.V with type t = R.t) = struct
  open R
  open V
  (** in polynomial, ((α₁,̣...,αₙ),c) : (int array * 'a) represent
      the monomial (m(α) c x^α where α = (α₁,̣...,αₙ) with Σαᵢ = d
      the degree of the monomial and m(α) is
      the multinomial coeficient d! / Π αᵢ!.

      Polynomials are represented a list ordered by the
      reverse of ocaml polymorphic comparison on the tuple of integers.

      The multinomial corresponds to Bernstein bases, giving a Bezier like
      representation of polynomial over the unit simplex *)

  type t = R.t
  type v = V.v
  type m = V.m
  type 'a p         = (int array * 'a) list
  type 'a pe        = 'a p

  (** we have polynomial with coeeficient in the field *)
  type polynomial   = R.t p

  (** and polynomial with vector coefficient, for the gradient *)
  type polynomial_v = v   p
  type polynomial_m = m   p

  (** Bombieri's norm, a.k.a Euclidian norm in Bernstein's basis *)
  let norm p =
    sqrt (List.fold_left (fun acc (_,c) -> acc +. c*.c) zero p)

  let iter_monomial gn homogen deg dim =
    let rec fn acc deg dim =
      if dim = 1 && homogen then
        begin
          let acc = List.rev (deg::acc) in
          gn (Array.of_list acc);
        end
      else if dim <= 0 then
        begin
          gn (Array.of_list acc);
        end
      else
        for i = deg downto 0 do
          fn (i::acc) (deg-i) (dim-1)
        done
    in
    fn [] deg dim

  let random homogen deg dim =
    let res = ref [] in
    let gn monom =
      res := (monom, of_float (Gaussian.random ())) :: !res
    in
    iter_monomial gn homogen deg dim;
    List.rev !res

  (** polynomial addition *)
  let (++) p1 p2 =
    let rec fn p1 p2 =
      match (p1,p2) with
      | ([], p)          | (p, [])                        -> p
      | ((l1,x1     )::p1, (l2,x2     )::p2) when l1 = l2 -> (l1, x1 +. x2)::fn p1 p2
      | ((l1,_ as c1)::p1, (l2,_      )::_ ) when l1 > l2 -> c1            ::fn p1 p2
      | ((_ ,_      )::_ , (_ ,_ as c2)::p2)              -> c2            ::fn p1 p2
    in fn p1 p2

  (** polynomial subtraction *)
  let (--) (p1:polynomial) (p2:polynomial) =
    let rec fn p1 p2 =
      match (p1,p2) with
        | (p, []) -> p
        | ((l1,x1     )::p1, (l2,x2)::p2) when l1 = l2 -> (l1, x1 -. x2)::fn p1 p2
        | ((l1,_ as c1)::p1, (l2,_ )::_ ) when l1 > l2 -> c1            ::fn p1 p2
        | (_               , (l2,x2)::p2)              -> (l2,   ~-. x2)::fn p1 p2
    in fn p1 p2

  (** polynomial addition *)
  let add_grad p1 p2 =
    let rec fn p1 p2 =
      match (p1,p2) with
      | ([], p)          | (p, [])                        -> p
      | ((l1,x1     )::p1, (l2,x2     )::p2) when l1 = l2 -> (l1, x1 +++ x2)::fn p1 p2
      | ((l1,_ as c1)::p1, (l2,_      )::_ ) when l1 > l2 -> c1             ::fn p1 p2
      | ((_ ,_      )::_ , (_ ,_ as c2)::p2)              -> c2             ::fn p1 p2
    in fn p1 p2

  (** polynomial subtraction *)
  let min_grad p1 p2 =
    let rec fn p1 p2 =
      match (p1,p2) with
        | (p, []) -> p
        | ((l1,x1     )::p1, (l2,x2)::p2) when l1 = l2 -> (l1, x1 --- x2)::fn p1 p2
        | ((l1,_ as c1)::p1, (l2,_ )::_ ) when l1 > l2 -> c1             ::fn p1 p2
        | (_               , (l2,x2)::p2)              -> (l2,    opp x2)::fn p1 p2
    in fn p1 p2

  (** multiplication by a constant *)
  let mul_cst x (p:polynomial) =
    List.map (fun (l,y) -> (l,y*.x)) p

  (** division by a constant *)
  let div_cst (p:polynomial) x = mul_cst (one /. x) p

  let normalise p =
    let n = norm p in div_cst p n

  (** dimension aka number of variable, check coherence of all monomials
      therefore trailing 0 must appears in the list of integer. *)
  let unsafe_dim p =
    match p with
    | (l,_)::_ -> Array.length l
    | _ -> 0

  let dim p =
    let d = unsafe_dim p in
    List.iter (fun (l,_) ->
        if Array.length l <> d then invalid_arg "inhomogeneous polynomial") p;
    d

  (** constant polynomial in d variables *)
  let cst d x = [(Array.make d 0, x)]

  let var_power i dim deg =
    Array.init dim (fun j -> if i = j then deg else 0)

  let cst_poly dim =
    let r = ref [] in
    for i = 0 to dim - 1 do
      let x2 = var_power i dim 2 in
      r := !r ++ [(x2, one)]
    done;
    !r

  (** degree *)
  let monomial_degree (l,_) = Array.fold_left (+) 0 l
  let unsafe_degree p = match p with [] -> 0 | m::_ -> monomial_degree m
  let degree p = List.fold_left (fun d m -> max d (monomial_degree m)) 0 p

  let vars p =
    let dim = dim p in
    let res = Array.make dim false in
    List.iter (fun (a,_) ->
        Array.iteri (fun i x -> if x > 0 then res.(i) <- true) a) p;
    res

  let use_all_vars p =
    Array.for_all (fun x -> x) (vars p)

  (** homogenisation *)
  let homogeneise p =
    let rec an d1 d2 =
      if d1 <= d2 then one else of_int d1 *. an (d1 - 1) d2
    in
    let d = degree p in
    let cmp x y = compare y x in
    if List.for_all (fun m -> monomial_degree m = d) p then (p,false) else
      (List.sort cmp (List.map (fun (l,c as m) ->
          let d0 = monomial_degree m in
          let d' = d - d0 in
          (Array.append l [|d'|], c *. an d' 1 /. an d d0)) p), true)

  (** increase polynomial dimension by one *)
  let increase_dim p =
    let cmp x y = compare y x in
    List.sort cmp (List.map (fun (l,c) ->
                       (Array.append l [|0|], c)) p)

  (** homogeneisation of a list of polynomials *)
  let homogeneise_many ps =
    let ps = List.map (fun p -> homogeneise p) ps in
    if List.exists snd ps then
      List.map (fun (p,b) -> if b then p else increase_dim p) ps
    else
      List.map fst ps

  (** general code to subdivise in two the simplex domain of a polynomial
      along the direction i <-> j *)
  let subdivise_gen zero avg p i j =
    let dim = unsafe_dim p in
    assert (i<>j);
    let (i,j) = if i < j then (i,j) else (j,i) in
    let l = Hashtbl.create 128 in
    List.iter (fun (m,c) ->
        let other = ref [] in
        Array.iteri (fun k n -> if k <> i && k <> j
                                then other := (k,n)::!other) m;
        let other = !other in
        let d = m.(i) + m.(j) in
        let (_,a) =
          try
            Hashtbl.find l other
          with Not_found ->
            let a = Array.make (d+1) zero in
            Hashtbl.add l other (d,a);
            (d,a)
        in
        a.(m.(i)) <- c) p;
    let divide a =
      let s = Array.length a in
      let a1 = Array.make s zero in
      let a2 = Array.make s zero in
      for i = 0 to s-1 do
        a1.(i) <- a.(0);
        a2.(s-i-1) <- a.(s-i-1);
        for j = 0 to s - i - 2 do
          a.(j) <- avg a.(j) a.(j+1)
        done;
      done;
      (a1,a2)
    in
    let p1 = ref [] in
    let p2 = ref [] in
    Hashtbl.iter (fun other (d,a) ->
        let (a1, a2) = divide a in
        for k = 0 to Array.length a - 1 do
          let m = Array.make dim 0 in
          m.(i) <- k;
          m.(j) <- d-k;
          List.iter (fun (l,e) -> m.(l) <- e) other;
          p1 := (m, a2.(k)) :: !p1;
          p2 := (m, a1.(k)) :: !p2
        done) l;
    let cmp x y = compare y x in
    (List.sort cmp !p1, List.sort cmp !p2)

  (** subdivise for scalar polynomial *)
  let subdivise p i j =
    subdivise_gen zero (fun x y -> (x +. y) /. of_int 2) p i j

  (** subdivise for gradient polynomial *)
  let subdivise_v p i j =
    let dim = unsafe_dim p in
    let zero = zero_v dim in
    subdivise_gen zero (fun x y -> (x +++ y) //. of_int 2) p i j

  (** opposite *)
  let ( ~--) : polynomial -> polynomial = List.map (fun (l,c) -> (l,-.c))

  (** binomial coefficient, note the type *)
  let rec binomial : int -> int -> R.t = fun a b ->
    if a = 0 || b = 0 then one else
      if a > b then binomial b a else
        (of_int (a + b) *. binomial (a - 1) b) /. (of_int a)

  (** binomial coefficient, int type *)
  let rec ibinomial : int -> int -> int = fun a b ->
    if a = 0 || b = 0 then 1 else
      if a > b then ibinomial b a else
        ((a + b) * ibinomial (a - 1) b) / a

  (** multinomial coefficient *)
  let multinomial : int array -> R.t = fun l ->
    let d = ref (of_int (Array.fold_left (+) 0 l)) in
    let r = ref one in
    for i = 0 to Array.length l - 2 do
      for k = 1 to l.(i) do
        r := !r *. !d /. of_int k;
        d := !d -. one
      done
    done;
    !r

  (** multinomial coefficient *)
  let qmultinomial : int array -> Q.t = fun l ->
    let d = ref (Q.of_int (Array.fold_left (+) 0 l)) in
    let r = ref Q.one in
    for i = 0 to Array.length l - 2 do
      for k = 1 to l.(i) do
        let open Q in
        r := !r * !d / of_int k;
        d := !d - one
      done
    done;
    !r


  let dimension p =
    let d = degree p in
    let (m,_) = List.hd p in
    let n = Array.length m - 1 in
    ibinomial n (n+d)

  (** monomial product *)
  let m_prod (l1,a1) (l2,a2) =
    let n1 = Array.length l1 and n2 = Array.length l2 in
    let (l1, l2) = if n1 > n2 then (l1, l2) else (l2, l1) in
    let l  = Array.mapi (fun i x -> if i < n2 then x + l2.(i) else x) l1 in
    (l, a1 *. a2 *. multinomial l1 *. multinomial l2 /. multinomial l)

  (** polynomial mulitplication *)
  let ( ** ) p1 p2 =
    List.fold_left (fun acc m1 ->
        List.fold_left (fun acc m2 -> acc ++ [m_prod m1 m2]) acc p2) [] p1

  (** monomial product *)
  let mg_prod (l1,a1) (l2,a2) =
    let n1 = Array.length l1 and n2 = Array.length l2 in
    let (l1, l2) = if n1 > n2 then (l1, l2) else (l2, l1) in
    let l  = Array.mapi (fun i x -> if i < n2 then x + l2.(i) else x) l1 in
    (l, (a1 *. multinomial l1 *. multinomial l2 /. multinomial l) **. a2)

  (** polynomial mulitplication *)
  let mul_grad p1 p2 =
    List.fold_left (fun acc m1 ->
        List.fold_left (fun acc m2 -> add_grad acc [mg_prod m1 m2]) acc p2) [] p1

  (** power of a polynomial *)
  let pow p n =
    let d = unsafe_dim p in
    let rec fn n =
      if n <= 0 then cst d one
      else if n = 1 then p
      else
        let q = fn (n lsr 1) in
        let q2 = q ** q in
        if n land 0x1 = 0 then q2 else q2 ** p
    in
    fn n

  type 'a hf =
    | HCst of 'a
    | HVar of 'a hf * 'a hf

  let split p i =
    let (p,q) = List.partition (fun (l,_) -> l.(i) <> 0) p in
    let p = List.map (fun (l,x) ->
                let l = Array.init (Array.length l) (fun j ->
                            if i = j then l.(i) - 1 else l.(j))
                in (l,x)) p
    in
    (p,q)

  let to_horner : type a. a -> (R.t -> a -> a) -> a p -> a hf =
    fun zero_c mul p ->
    let rec fn m d e i p =
      match p with
      | [] -> HCst zero_c
      | [(l,x)] when Array.for_all ((=) 0) l -> HCst (mul m x)
      | _ ->
         let (p,q) = split p i in
         let q = fn m d zero (i+1) q in
         let d' = d +. one in
         let e' = e +. one in
         let m' = m *. d' /. e' in
         let p = fn m' d' e' i p in
         HVar(p,q)
    in
    fn one zero zero 0 p

  let to_horner_m p =
    let (l,c) = match p with
      | [] -> assert false
      | (_,x)::_ -> (Array.length x, Array.length x.(0))
    in
    to_horner (zero_m l c) ( ***. ) p

  let to_horner_v p =
    let l = match p with
      | [] -> assert false
      | (_,x)::_ -> Array.length x
    in
    to_horner (zero_v l) ( **. ) p

  let to_horner = to_horner zero ( *. )

  (** substitution *)
  let subst d p qs =
    let rec fn p qs = match (p,qs) with
      | (HCst x, _) -> if x =. zero then [] else cst d x
      | (HVar (p,q), q0::qs') ->
         q0 ** fn p qs ++ fn q qs'
      | (HVar _, []) -> assert false
    in
    fn p qs
(*
    List.fold_left (fun acc (l,x) ->
        List.fold_left2 (fun acc e q ->
            acc ** pow q e) (cst d (multinomial l *. x)) (Array.to_list l) qs
        ++ acc) [] p
 *)

  (** map, that removes the case when Exit is raised *)
  let filter_map f l =
    let rec fn = function
      | []   -> []
      | x::l -> let r = fn l in try f x::r with Exit -> r
    in fn l

  (** decrease one of the exponent in a monomial, raise Exit if 0 *)
  let decr l i =
    Array.mapi (fun j n -> if i = j then if n = 0 then raise Exit else n - 1
                           else n) l

  (** partial: partial derivative of p in the ith variable *)
  let partial (p:polynomial) i =
    match p with
    | [] -> []
    | p  ->
       let deg = unsafe_degree p in
       filter_map (fun (l,c) -> (decr l i, of_int deg *. c)) p

  (** gradient as a polynomial with vector as coefficients *)
  let gradient (p:polynomial) =
    let dim = unsafe_dim p in
    let ps =  Array.init dim (fun i -> partial p i) in
    let res = ref [] in
    try
      while true do
        let l = Array.fold_left (fun l p ->
                    match (l, p) with
                    | None,  (l,_)::_ -> Some l
                    | Some l,(l',_)::_ when compare l l' < 0 -> Some l'
                    | _ -> l) None ps
        in
        match l with
        | None -> raise Exit
        | Some l ->
        let c = Array.init dim (fun i ->
                    match ps.(i) with
                    | (l',c) :: p when l = l' -> ps.(i) <- p; c
                    | _ -> zero)
        in
        res := (l,c) :: !res
      done;
      assert false
    with Exit -> List.rev !res

  let tgrad p =
    let dim = unsafe_dim p in
    let d = of_int (unsafe_degree p) in
    let n2 = List.init dim (fun i -> (var_power i dim 2, one)) in
    let nd = List.init dim (fun i ->
                (var_power i dim 1,
                 Array.init dim (fun j -> if i = j then d else zero)))
    in
    min_grad (mul_grad n2 (gradient p)) (mul_grad p nd)

  (** gradient as a polynomial with vector as coefficients *)
  let hessian (p:polynomial) =
    let dim = unsafe_dim p in
    let pss =  Array.init dim
                (fun i -> Array.init dim
                            (fun j -> partial (partial p i) j))
    in
    let res = ref [] in
    try
      while true do
        let l = Array.fold_left (fun l ps ->
                    Array.fold_left (fun l p ->
                        match (l, p) with
                        | None,  (l,_)::_ -> Some l
                        | Some l,(l',_)::_ when compare l l' < 0 -> Some l'
                        | _ -> l) l ps) None pss
        in
        match l with
        | None -> raise Exit
        | Some l ->
           let c = Array.init dim (fun i ->
                       (Array.init dim (fun j ->
                            match pss.(i).(j) with
                            | (l',c) :: p when l = l' -> pss.(i).(j) <- p; c
                            | _ -> zero)))
           in
           res := (l,c) :: !res
      done;
      assert false
    with Exit -> List.rev !res

  let first_deg p =
    let count l = Array.fold_left (fun b n ->
                      if n = 0 then b else
                        if n > 0 && b then raise Exit else true)
                    false l
    in
    filter_map
      (fun (l,c) ->
        assert (count l);
        let l = Array.map (fun x -> if x <> 0 then 1 else 0) l in
        (l,c)) p

  (** for evaluation, we memoize the last evaluation *)

  let pre_eval fn p =
    List.map (fun (l,x) -> (l, fn (multinomial l) x)) p

  let all_power d x =
    let r = Array.make (d+1) one in
    for i = 1 to d do r.(i) <- r.(i-1) *. x done;
    r

  (** evaluation of a polynomial *)
  let last_eval = ref([],[||],zero)
  let eval (p:polynomial) x =
    let (lp,lx,r) = !last_eval in
    if  p == lp && x == lx then r else
      begin
        let d = unsafe_degree p in
        let xd = Array.map (all_power d) x in
        let r = ref zero in
        List.iter (fun (l,c) ->
            r := !r +. c *. (
                     let z = ref one in
                     Array.iteri (fun i e -> z := !z *. xd.(i).(e)) l;
                     !z)) p;
        last_eval := (p,x,!r);
        !r
      end

  (** evaluation of a polynomial gradient *)
  let last_eval_grad = ref([],[||],[||])
  let eval_grad dp x =
    let (ldp,lx,r) = !last_eval_grad in
    if dp == ldp && x == lx then r else
      begin
        let d = unsafe_degree dp in
        let xd = Array.map (all_power d) x in
        let res = zero_v (unsafe_dim dp) in
        List.iter (fun (l,c) ->
            let z = ref one in
            Array.iteri (fun i e -> z := !z *. xd.(i).(e)) l;
            combqo res !z c) dp;
        last_eval_grad := (dp,x,res);
        res
      end

  (** evaluation of a polynomial tangential gradient *)
  let last_eval_tgrad = ref([],[||],([||],zero))
  let eval_tgrad dp x =
    let (ldp,lx,r) = !last_eval_tgrad in
    if dp == ldp && x == lx then r else
      begin
        let g = eval_grad dp x in
        let p = g *.* x in
        let r = comb one g (-. p) x in
        let r = (r,p) in
        last_eval_tgrad := (dp,x,r);
        r
      end

  (** evaluation of a polynomial hessian matrix *)
  let last_eval_hess = ref([],[||],[||])
  let eval_hess hp x =
    let (lhp,lx,r) = !last_eval_hess in
    if hp == lhp && x == lx then r else
      begin
        let dim = unsafe_dim hp in
        let d = unsafe_degree hp in
        let xd = Array.map (all_power d) x in
        let r = zero_m dim dim in
        List.iter (fun (l,c) ->
            let z = ref one in
            Array.iteri (fun i e -> z := !z *. xd.(i).(e)) l;
            mcombq one r !z c) hp;
        last_eval_hess := (hp,x,r);
        r
      end

  (** evaluation of a polynomial "tangential hessian", i.e.
      a matrix that can be used to solve tangential gradient = 0 *)
  let last_eval_thess = ref ([],[||],([||],[||],zero))
  let eval_thess hp x =
    let (lhp,lx,r) = !last_eval_thess in
    if hp == lhp && x == lx then r else
      begin
        let dim = unsafe_dim hp in
        let deg = unsafe_degree hp + 2 in
        let h = eval_hess hp x in
        let dmg = h *** x in
        let g  = dmg //. of_int (deg - 1) in
        let dp = g *.* x in
        let tg = comb one g (-. dp) x in
        let r =
          Array.init dim (fun i ->
              Array.init dim (fun j ->
                  (if h <> [||] then h.(i).(j) else zero)
                  -. dmg.(i) *. x.(j)
                  -. of_int deg *. x.(i) *. g.(j)
                  -.  (if i = j then dp else zero)
                  +. (one +. of_int (deg + 1) *. dp) *. x.(i) *. x.(j)
                  ))
        in
        let r = (r,tg,dp) in
        last_eval_thess := (hp,x,r);
        r

      end

  (** third version, unlimited ! *)
  let print_monomial times vars ch l =
    Array.iteri (fun i e ->
        if e <> 0 then
          begin
            if times then fprintf ch "*";
            if e > 1 then fprintf ch "%s^%d" vars.(i) e
            else  fprintf ch "%s" vars.(i)
          end) l

  let mkvars vars p =
    match vars with
      | Some v -> v
      | None -> Array.init (unsafe_dim p) (fun i -> "X" ^ string_of_int i)

  let print_polynome ?(times=false) ?(q=false) ?vars ch p =
    let vars = mkvars vars p in
    let first = ref true in
    List.iter (fun (l,c) ->
        if c <> zero then
          begin
            if not !first then fprintf ch " + ";
            first := false;
            if q then
              fprintf ch "%s%a" (Q.to_string (Q.mul (R.to_q c) (qmultinomial l)))
                (print_monomial times vars) l
            else
              fprintf ch "%a%a" print (c *. multinomial l)
                (print_monomial times vars) l;
          end) p

  let print_gradient ?vars ch p =
    let vars = mkvars vars p in
    let first = ref true in
    List.iter (fun (l,c) ->
        if Array.exists (fun x -> x <>. zero) c then
          begin
            if not !first then fprintf ch " + ";
            first := false;
            fprintf ch "%a %a" print_vector c
              (print_monomial false vars) l;
          end) p

  let print_hessian ?vars ch p =
    let vars = mkvars vars p in
    let first = ref true in
    List.iter (fun (l,c) ->
        if Array.exists (Array.exists (fun x -> x <>. zero)) c then
          begin
            if not !first then fprintf ch " + ";
            first := false;
            fprintf ch "%a %a" print_matrix c
              (print_monomial false vars) l;
          end) p

  let plane : R.t p -> R.t array = fun p ->
    let count l =
      let r = Array.fold_left (fun b n ->
                  if n = 0 then b else
                    if n > 0 && b then raise Exit else true)
                false l
      in
      if not r then
        begin
          List.iter (fun (l,c) -> printf "(%a,%a) " print_int_array l print c) p;
          printf "\n%a\n%!" (fun p -> print_polynome p) p;
        end;
      r
    in
    Array.of_list (filter_map (fun (l,c) -> assert (count l); c) p)

  let transform p s1 s2 =
    let dim = Array.length s1 in
    assert (Array.length s1.(0) = dim);
    assert (Array.length s2 = dim);
    assert (Array.length s2.(0) = dim);
    let m = Array.init dim (fun i -> pcoord s2.(i) s1) in
    let q = List.init dim (fun j ->
                List.init dim (fun i ->
                    let v = var_power i dim 1 in
                    let c = m.(i).(j) in
                    (v, c)))
    in
    subst dim p q

  let lift_linear p deg =
    let dim = Array.length p in
    let p1 = ref [] in
    let gn monomial =
      let res = ref zero in
      Array.iteri (fun i k ->
          res := !res +. (of_int k /. of_int deg) *. p.(i)) monomial;
      p1 := (monomial, !res) :: !p1
    in
    iter_monomial gn true deg dim

end

module type B = sig
  type t
  type v
  type m
  type 'a p = (int array * 'a) list
  type 'a pe
  type polynomial = t p
  type polynomial_v = v p
  type polynomial_m = m p
  type 'a hf

  val print_polynome : ?times:bool -> ?q:bool -> ?vars:string array
                       -> formatter -> polynomial -> unit
  val print_gradient : ?vars:string array -> formatter -> polynomial_v -> unit
  val print_hessian  : ?vars:string array -> formatter -> polynomial_m -> unit

  val multinomial : int array -> t

  val dim : 'a p -> int
  val degree : 'a p -> int
  val dimension : 'a p -> int
  val norm : polynomial -> t
  val normalise : polynomial -> polynomial
  val random : bool -> int -> int -> polynomial
  val use_all_vars : 'a p -> bool

  val cst : int -> 'a -> 'a p
  val var_power : int -> int -> int -> int array

  val pre_eval : (t -> 'a -> 'a) -> 'a p -> 'a pe
  val eval : t pe -> v -> t
  val eval_grad : v pe -> v -> v
  val eval_tgrad : v pe -> v -> v * t
  val eval_hess : m pe -> v -> m
  val eval_thess : m pe -> v -> m * v * t

  val ( ++ ) : polynomial -> polynomial -> polynomial
  val ( -- ) : polynomial -> polynomial -> polynomial
  val ( ** ) : polynomial -> polynomial -> polynomial
  val pow : polynomial -> int -> polynomial

  val to_horner : polynomial -> t hf
  val to_horner_v : polynomial_v -> v hf
  val to_horner_m : polynomial_m -> m hf
  val homogeneise : polynomial -> polynomial * bool
  val homogeneise_many : polynomial list -> polynomial list
  val transform : t hf -> m -> m -> polynomial
  val subdivise : polynomial -> int -> int -> polynomial * polynomial
  val subdivise_v : polynomial_v -> int -> int -> polynomial_v * polynomial_v
  val partial : polynomial -> int -> polynomial

  val gradient  : polynomial -> polynomial_v
  val tgrad     : polynomial -> polynomial_v
  val hessian   : polynomial -> polynomial_m
  val plane     : t p -> t array
  val first_deg : 'a p -> 'a p

  val cst_poly : int -> polynomial

end
