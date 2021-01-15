open Printing
open FieldGen

module Make(R:S) (V:Vector.V with type t = R.t) = struct
  open R
  open V
  (** (m(α) c x^α where α = (α₁,̣...,αₙ) with Σαᵢ = d the degree and m(α) is
      the multinimial coeficient d! / Π αᵢ! is represented by
      [(α, c)]. The sum of the monomial is a list ordered by the
      reverse of ocaml polymorphic comparison.

      The multinomial corresponds to Bernstein bases, giving a Bezier like
      representation of polynomial over a simplex *)

  type t = R.t
  type v = V.v
  type m = V.m
  type 'a p         = (int array * 'a) list
  type polynomial   = R.t p
  type polynomial_v = v   p

  (** polynomial addition *)
  let (++) (p1:polynomial) (p2:polynomial) =
    let rec fn p1 p2 =
      match (p1,p2) with
      | ([], p)          | (p, [])                        -> p
      | ((l1,x1     )::p1, (l2,x2     )::p2) when l1 = l2 -> (l1, x1 +. x2)::fn p1 p2
      | ((l1,_ as c1)::p1, (l2,_      )::_ ) when l1 > l2 -> c1            ::fn p1 p2
      | ((_ ,_      )::_ , (_ ,_ as c2)::p2)              -> c2            ::fn p1 p2
    in fn p1 p2

  (** polynomial addition *)
  let v_add (p1:polynomial_v) (p2:polynomial_v) =
    let rec fn p1 p2 =
      match (p1,p2) with
      | ([], p)          | (p, [])                        -> p
      | ((l1,x1     )::p1, (l2,x2     )::p2) when l1 = l2 -> (l1, x1 +++ x2)::fn p1 p2
      | ((l1,_ as c1)::p1, (l2,_      )::_ ) when l1 > l2 -> c1            ::fn p1 p2
      | ((_ ,_      )::_ , (_ ,_ as c2)::p2)              -> c2            ::fn p1 p2
    in fn p1 p2

  let (--) (p1:polynomial) (p2:polynomial) =
    let rec fn p1 p2 =
      match (p1,p2) with
        | (p, []) -> p
        | ((l1,x1     )::p1, (l2,x2)::p2) when l1 = l2 -> (l1, x1 -. x2)::fn p1 p2
        | ((l1,_ as c1)::p1, (l2,_ )::_ ) when l1 > l2 -> c1            ::fn p1 p2
        | (_               , (l2,x2)::p2)              -> (l2,   ~-. x2)::fn p1 p2
    in fn p1 p2

  let mul_cst x (p:polynomial) =
    List.map (fun (l,y) -> (l,y*.x)) p

  let div_cst (p:polynomial) x = mul_cst (one /. x) p

  (** dimension aka number of variable, check coherence of all monomials
      therefore trailing 0 must appears in the list of integer. *)
  let dim p =
    let d = match p with
      | (l,_)::_ -> Array.length l
      | _ -> invalid_arg "null polynomial"
    in
    List.iter (fun (l,_) ->
        if Array.length l <> d then invalid_arg "inhomogeneous polynomial") p;
    d

  (** constant polynomial in d variables *)
  let cst d x = [(Array.make d 0, x)]

  let var_power i dim deg =
    Array.init dim (fun j -> if i = j then deg else 0)

  (** degree *)
  let monomial_degree (l,_) = Array.fold_left (+) 0 l
  let degree p = List.fold_left (fun d m -> max d (monomial_degree m)) 0 p

  (** homogenisation *)
  let homogeneisation p =
    let rec an d1 d2 =
      if d1 <= d2 then one else of_int d1 *. an (d1 - 1) d2
    in
    let d = degree p in
    if List.for_all (fun m -> monomial_degree m = d) p then (p,false) else
      (List.map (fun (l,c as m) ->
          let d0 = monomial_degree m in
          let d' = d - d0 in
          (Array.append l [|d'|], c *. an d' 1 /. an d d0)) p, true)

  (** opposite *)
  let ( ~--) : polynomial -> polynomial = List.map (fun (l,c) -> (l,-.c))

  (** binomial coefficient, note the type *)
  let rec binomial : int -> int -> R.t = fun a b ->
    if a = 0 || b = 0 then one else
      if a > b then binomial b a else
        (of_int (a + b) *. binomial (a - 1) b) /. (of_int a)

  (** multinomial coefficient *)
  let multinomial : int array -> R.t = fun l ->
    let d = Array.fold_left (+) 0 l in
    let l = List.sort compare (Array.to_list l) in
    let rec fn d = function
      | [_] | [] -> one
      | 0::l -> fn d l
      | a::l -> (of_int d *. fn (d-1) (a-1::l)) /. of_int a
    in
    fn d l

  (** monome product *)
  let m_prod (l1,a1) (l2,a2) =
    let n1 = Array.length l1 and n2 = Array.length l2 in
    let (l1, l2) = if n1 > n2 then (l1, l2) else (l2, l1) in
    let l  = Array.mapi (fun i x -> if i < n2 then x + l2.(i) else x) l1 in
    (l, a1 *. a2 *. multinomial l1 *. multinomial l2 /. multinomial l)

  (** polynomial multplication *)
  let ( ** ) p1 p2 =
    List.fold_left (fun acc m1 ->
        List.fold_left (fun acc m2 -> acc ++ [m_prod m1 m2]) acc p2) [] p1

  (** monome product *)
  let mcv_prod x (l1,a1) (l2,a2) =
    let n1 = Array.length l1 and n2 = Array.length l2 in
    let (l1, l2) = if n1 > n2 then (l1, l2) else (l2, l1) in
    let l  = Array.mapi (fun i x -> if i < n2 then x + l2.(i) else x) l1 in
    let c = x *. a1 *. multinomial l1 *. multinomial l2 /. multinomial l in
    (l, Array.map (fun x -> c *. x) a2)

  (** polynomial multplication *)
  let cv_prod x p1 p2 =
    List.fold_left (fun acc m1 ->
        List.fold_left (fun acc m2 -> v_add acc [mcv_prod x m1 m2]) acc p2) [] p1

  (** monome product *)
  let mvv_prod (l1,a1) (l2,a2) =
    let n1 = Array.length l1 and n2 = Array.length l2 in
    let (l1, l2) = if n1 > n2 then (l1, l2) else (l2, l1) in
    let l  = Array.mapi (fun i x -> if i < n2 then x + l2.(i) else x) l1 in
    let c = multinomial l1 *. multinomial l2 /. multinomial l in
    (l, c *. (a1 *.* a2))

  (** polynomial multplication *)
  let vv_prod p1 p2 =
    List.fold_left (fun acc m1 ->
        List.fold_left (fun acc m2 -> acc ++ [mvv_prod m1 m2]) acc p2) [] p1

  (** power of a polynomial *)
  let pow p n =
    let d = dim p in
    let rec fn n =
      if n <= 0 then cst d one
      else if n = 1 then p
      else
        let q = fn (n lsr 1) in
        let q2 = q ** q in
        if n land 0x1 = 0 then q2 else q2 ** p
    in
    fn n

  (** substitution *)
  let subst p qs =
    let d = dim p in
    List.fold_left (fun acc (l,x) ->
        List.fold_left2 (fun acc e q ->
            acc ** pow q e) (cst d (multinomial l *. x)) (Array.to_list l) qs
        ++ acc) [] p

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

  (** partial: partial derivative of p in the ith variable,
      we do not multiply by the degree, it is not very important.
      Recall that with Bernstein, no multiplication by the exponent,
      but by the degree, which is the same for all monomials *)
  let partial (p:polynomial) i =
    filter_map (fun (l,c) -> (decr l i, c)) p

  (** gradient *)
  let gradient (p:polynomial) =
    Array.init (dim p) (fun i -> partial p i)

  (** gradient as a polynomial with vector as coefficients *)
  let tgradient (p:polynomial) =
    (* collect all monomials *)
    let ps = gradient p in
    let dim = Array.length ps in
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

  let integrate_simplex ?(filter=fun _ -> true) p =
    (* missing constante vol(s) / binomial deg (deg + dim - 1) *)
    List.fold_left (fun acc (l,x) -> if filter l then x +. acc else acc) zero p

  let plane p =
    let count l = Array.fold_left (fun b n ->
                      if n = 0 then b else
                        if n > 0 && b then raise Exit else true)
                    false l
    in
    Array.of_list (filter_map (fun (l,c) -> assert (count l); c) p)

  let eval (p:polynomial) x =
    List.fold_left (fun acc (l,c) ->
        acc +. c *. multinomial l *. (
          let z = ref one in
          Array.iteri (fun i e -> z := !z *. R.pow x.(i) e) l;
          !z
        )) zero p

  let eval_grad p x =
    List.fold_left (fun acc (l,c) ->
        acc +++ (multinomial l *. (
          let z = ref one in
          Array.iteri (fun i e -> z := !z *. R.pow x.(i) e) l;
          !z)) **. c
        ) (zero_v (dim p)) p

  let digho (p:polynomial) epsilon p1 x p2 y =
    let e2 = epsilon *. epsilon in
    if cmp p1 zero = 0 then x
    else if cmp p2 zero = 0 then y
    else begin
        assert (cmp (p1 *. p2) zero < 0);
        let h = one /. of_int 2 in
        let rec fn p1 x p2 y =
          assert (cmp p1 zero < 0);
          assert (cmp p2 zero > 0);
          let z = comb h x h y in
          let p3 = eval p z in
          if cmp (dist2 x y) e2 < 0 then z else
          let c = cmp p3 zero in
          if c = 0 then z
          else if c < 0 then fn p3 z p2 y
          else fn p1 x p3 z
        in
        if cmp p1 zero < 0 then fn p1 x p2 y else fn p2 y p1 x
      end
  (** first version, limited to dimension 26 ! *)
  let print_polynome26 ch p =
    let first = ref true in
    List.iter (fun (l,c) ->
        if c <> zero then
          begin
            if not !first then fprintf ch " + ";
            first := false;
            fprintf ch "%a " print c;
            Array.iteri (fun i e ->
                if e <> 0 then
                  if e > 1 then
                    fprintf ch "%c^%d "
                                   (Char.chr (Char.code 'a' + i)) e
                  else
                    fprintf ch "%c "
                                   (Char.chr (Char.code 'a' + i))) l;
          end) p
  (** second version, limited to dimension 3, starts with 'x' ! *)
  let print_polynome10 ch p =
    let first = ref true in
    List.iter (fun (l,c) ->
        if c <> zero then
          begin
            if not !first then fprintf ch " + ";
            first := false;
            fprintf ch "%a " print c;
            Array.iteri (fun i e ->
                if e <> 0 then
                  if e > 1 then
                    fprintf ch "%c^%d "
                                   (Char.chr (Char.code 'x' + i)) e
                  else
                    fprintf ch "%c"
                                   (Char.chr (Char.code 'x' + i))) l;
          end) p


  (** third version, unlimited ! *)
  let print_monomial ch l =
    Array.iteri (fun i e ->
        if e <> 0 then
          if e > 1 then fprintf ch "X%d^%d " i e
          else  fprintf ch "X%d " i) l

  let print_polynome ch p =
    let first = ref true in
    List.iter (fun (l,c) ->
        if c <> zero then
          begin
            if not !first then fprintf ch " + ";
            first := false;
            fprintf ch "%a %a" print c
              print_monomial l;
          end) p

  let print_gradient ch p =
    let first = ref true in
    List.iter (fun (l,c) ->
        if Array.exists (fun x -> x <>. zero) c then
          begin
            if not !first then fprintf ch " + ";
            first := false;
            fprintf ch "%a %a" print_vector c
              print_monomial l;
          end) p

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
    subst p q

end [@@inlined always]

module type B = sig
  type t
  type v
  type m
  type 'a p = (int array * 'a) list
  type polynomial = t p
  type polynomial_v = v p

  val print_polynome : formatter -> polynomial -> unit
  val print_gradient : formatter -> polynomial_v -> unit

  val dim : 'a p -> int
  val degree : 'a p -> int
  val cst : int -> 'a -> 'a p
  val var_power : int -> int -> int -> int array

  val eval : polynomial -> v -> t
  val eval_grad : polynomial_v -> v -> v

  val ( ++ ) : polynomial -> polynomial -> polynomial
  val ( -- ) : polynomial -> polynomial -> polynomial
  val ( ** ) : polynomial -> polynomial -> polynomial
  val pow : polynomial -> int -> polynomial

  val v_add : polynomial_v -> polynomial_v -> polynomial_v
  val cv_prod : t -> polynomial -> polynomial_v -> polynomial_v
  val vv_prod : polynomial_v -> polynomial_v -> polynomial

  val subst : polynomial -> polynomial list -> polynomial
  val homogeneisation : polynomial -> polynomial * bool
  val transform : polynomial -> m -> m -> polynomial

  val tgradient : polynomial -> polynomial_v
  val plane : 'a p -> 'a array

  val digho : polynomial -> t -> t -> v -> t -> v -> v
end
