module Make(R:Field.S) = struct
  open R
  module V = Vector.Make(R)

  (** (m(α) c x^α where α = (α₁,̣...,αₙ) with Σαᵢ = d the degree and m(α) is
      the multinimial coeficient d! / Π αᵢ! is represented by
      [(α, c)]. The sum of the monomial is a list ordered by the
      reverse of ocaml polymorphic comparison.

      The multinomial corresponds to Bernstein bases, giving a Bezier like
      representation of polynomial over a simplex *)
  type polynomial = (int list * t) list

  (** polynomial addition *)
  let (++) (p1:polynomial) (p2:polynomial) =
    let rec fn p1 p2 =
      match (p1,p2) with
      | ([], p)          | (p, [])                        -> p
      | ((l1,x1     )::p1, (l2,x2     )::p2) when l1 = l2 -> (l1, x1 +. x2)::fn p1 p2
      | ((l1,_ as c1)::p1, (l2,_      )::_ ) when l1 > l2 -> c1            ::fn p1 p2
      | ((l1,_      )::_ , (l2,_ as c2)::p2)              -> c2            ::fn p1 p2
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
      | (l,_)::_ -> List.length l
      | _ -> invalid_arg "null polynomial"
    in
    List.iter (fun (l,_) ->
        if List.length l <> d then invalid_arg "inhomogeneous polynomial") p;
    d

  (** constant polynomial in d variables *)
  let cst d x =
    let rec fn acc n = if n <= 0 then acc else fn (0::acc) (n-1) in
    [(fn [] d, x)]

  let var_power i dim deg =
    Array.to_list
      (Array.init dim (fun j -> if i = j then deg else 0))

  (** degree, only allows for homogeneous polynomials *)
  let degree p =
    let d = match p with
      | (l,_)::_ -> List.fold_left (+) 0 l
      | _ -> invalid_arg "null polynomial"
    in
    List.iter (fun (l,_) ->
        if List.fold_left (+) 0 l <> d then invalid_arg "inhomogeneous polynomial") p;
    d

  (** opposite *)
  let ( ~--) : polynomial -> polynomial = List.map (fun (l,c) -> (l,-.c))

  (** binomial coefficient, note the type *)
  let rec binomial : int -> int -> t = fun a b ->
    if a = 0 || b = 0 then one else
      if a > b then binomial b a else
        (of_int (a + b) *. binomial (a - 1) b) /. (of_int a)

  (** multinomial coefficient *)
  let multinomial : int list -> t = fun l ->
    let d = List.fold_left (+) 0 l in
    let l = List.sort compare l in
    let rec fn d = function
      | [_] | [] -> one
      | 0::l -> fn d l
      | a::l -> (of_int d *. fn (d-1) (a-1::l)) /. of_int a
    in
    fn d l

  (** monome product *)
  let ( *** ) (l1,a1) (l2,a2) =
    let l  = List.map2 (fun x y -> x + y) l1 l2 in
    (l, a1 *. a2 *. multinomial l1 *. multinomial l2 /. multinomial l)

  (** polynomial multplication *)
  let rec ( ** ) p1 p2 =
    List.fold_left (fun acc m1 ->
        List.fold_left (fun acc m2 -> acc ++ [m1 *** m2]) acc p2) [] p1

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
            acc ** pow q e) (cst d (multinomial l *. x)) l qs
        ++ acc) [] p

  (** map, that removes the case when Exit is raised *)
  let filter_map f l =
    let rec fn = function
      | []   -> []
      | x::l -> try f x::fn l with Exit -> fn l
    in fn l

  (** decrease one of the exponent in a monomial, raise Exit if 0 *)
  let decr l i =
    let rec fn i acc l = match (i,l) with
      | 0, (0::l) -> raise Exit
      | 0, (n::l) -> List.rev_append acc ((n-1)::l)
      | i, (n::l) -> fn (i-1) (n::acc) l
      | _, []     -> assert false
    in fn i [] l

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
    let ls = Array.fold_left (fun acc p ->
                 List.fold_left (fun acc (l,_) -> l :: acc) acc p) [] ps
    in
    let compare l l' = compare l' l in
    let ls = List.sort_uniq compare ls in
    List.map (fun l ->
        let c = Array.mapi (fun i p ->
                    match p with
                    | (l',c) :: q when l = l' -> ps.(i) <- q; c
                    | _ -> zero) ps
        in (l, c)) ls

  let integrate_simplex ?(filter=fun _ -> true) p =
    (* missing constante vol(s) / binomial deg (deg + dim - 1) *)
    List.fold_left (fun acc (l,x) -> if filter l then x +. acc else acc) zero p

  let plane (p:polynomial) =
    let deg = degree p in
    Array.init (dim p) (fun i -> List.assoc (var_power i (dim p) deg) p)

  let eval (p:polynomial) x =
    List.fold_left (fun acc (l,c) ->
        acc +. c *. multinomial l *. (
          let z = ref one in
          List.iteri (fun i e -> z := !z *. R.pow x.(i) e) l;
          !z
        )) zero p

  let eval_grad p x =
    let open V in
    List.fold_left (fun acc (l,c) ->
        acc +++ (multinomial l *. (
          let z = ref one in
          List.iteri (fun i e -> z := !z *. R.pow x.(i) e) l;
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
          let z = V.comb h x h y in
          let p3 = eval p z in
          if cmp (V.dist2 x y) e2 < 0 then z else
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
            if not !first then Printf.fprintf ch " + ";
            first := false;
            Printf.fprintf ch "%a " print c;
            List.iteri (fun i e ->
                if e <> 0 then
                  if e > 1 then
                    Printf.fprintf ch "%c^%d "
                                   (Char.chr (Char.code 'a' + i)) e
                  else
                    Printf.fprintf ch "%c "
                                   (Char.chr (Char.code 'a' + i))) l;
          end) p
  (** second version, limited to dimension 3, starts with 'x' ! *)
  let print_polynome10 ch p =
    let first = ref true in
    List.iter (fun (l,c) ->
        if c <> zero then
          begin
            if not !first then Printf.fprintf ch " + ";
            first := false;
            Printf.fprintf ch "%a " print c;
            List.iteri (fun i e ->
                if e <> 0 then
                  if e > 1 then
                    Printf.fprintf ch "%c^%d "
                                   (Char.chr (Char.code 'x' + i)) e
                  else
                    Printf.fprintf ch "%c"
                                   (Char.chr (Char.code 'x' + i))) l;
          end) p


  (** third version, unlimited ! *)
  let print_polynome ch p =
    let first = ref true in
    List.iter (fun (l,c) ->
        if c <> zero then
          begin
            if not !first then Printf.fprintf ch " + ";
            first := false;
            Printf.fprintf ch "%a " print c;
            List.iteri (fun i e ->
                if e <> 0 then
                  if e > 1 then Printf.fprintf ch "X%d^%d " i e
                  else  Printf.fprintf ch "X%d " i) l;
          end) p

  (** third version, unlimited ! *)
  let print_polynome' ch p =
    let first = ref true in
    List.iter (fun ((l,(x,y)),c) ->
          begin
            if not !first then Printf.fprintf ch " + ";
            first := false;
            Printf.fprintf ch "%a " print c;
            List.iteri (fun i e ->
                if e <> 0 then
                  if e > 1 then Printf.fprintf ch "X%d^%d " i e
                  else  Printf.fprintf ch "X%d " i) (x::y::l);
          end) p

  let transform p s1 s2 =
    let dim = Array.length s1 in
    assert (Array.length s1.(0) = dim);
    assert (Array.length s2 = dim);
    assert (Array.length s2.(0) = dim);
    let m = Array.init dim (fun i -> V.pcoord s2.(i) s1) in
    let q = List.init dim (fun j ->
                List.init dim (fun i ->
                    let v = var_power i dim 1 in
                    let c = m.(i).(j) in
                    (v, c)))
    in
    subst p q

  let positive p =
    Printf.printf "P = %a\n%!" print_polynome p;
    let dim = dim p in
    let deg = degree p in
    if deg < 2 then List.for_all (fun (_,c) -> c >=. zero) p else
    let res = ref [] in
    let rec fn acc dim degree =
      if dim = 1 then res := (degree::acc)::!res else
        for i = 0 to degree do
          fn (i::acc) (dim - 1) (degree-i)
        done;
    in
    fn [] dim deg;
    let monomials = !res in
    let mat = List.map (fun l -> [l,one]) monomials in
    let mat = ref (List.rev mat) in
    List.iter (fun (l,c) ->
        if c <. zero then
          for i = 0 to dim - 1 do
            for j = i+1 to dim - 1 do
              if List.nth l i >= 1 && List.nth l j >= 1 then
                let lx2 = List.mapi (fun k x -> if i = k then x - 1 else if j = k then x + 1 else x) l in
                let ly2 = List.mapi (fun k x -> if j = k then x - 1 else if i = k then x +1 else x) l in
                mat := [(lx2,one); (ly2,one); (l,~-.one)] :: !mat
            done
          done) p;
    let mat = List.rev !mat in
    let m = List.map (fun ls -> List.map (fun l -> try List.assoc l ls with Not_found -> zero) monomials) mat in
    let m = Array.of_list (List.map Array.of_list m) in
    let b = List.map (fun l -> try List.assoc l p with Not_found -> zero) monomials in
    let b = Array.of_list b in
    let pos = Array.make (Array.length m) true in
    V.(try let _s = solve_pos m b pos in
           V.(Printf.printf "%a X = %a\n  ==>%a\n%!" print_matrix m print_vector b print_vector _s);

           true with Not_found -> false)



(*
    let _ = assert (positive [ ([2;0],one); ([1;1],~-. one /. of_int 2); ([0;2], one) ])
    let _ = assert (positive [ ([2;0;0],one); ([1;1;0],~-. one /. of_int 2); ([0;2;0], one) ])
 *)
end
