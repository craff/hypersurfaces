module Make(R:Field.SPlus) = struct

  open R

  type func = { name : string; eval : R.t -> R.t }

  type poly_rec =
    { name : string
    ; dim : int
    ; vars: string list
    ; poly : polynomial
    ; bern : B.polynomial
    ; hdim : int
    ; mutable triangulation : R.t Array.t Array.t list
    ; mutable edges : R.t Array.t Array.t list }

  and polynomial =
    | Cst of R.t
    | Var of string
    | Pow of polynomial * int
    | Sum of polynomial * polynomial
    | Sub of polynomial * polynomial
    | Pro of polynomial * polynomial
    | App of poly_rec * polynomial list
    | Fun of func * polynomial

  let polys : (string, poly_rec) Hashtbl.t = Hashtbl.create 101

  let eval_cst p =
    let rec fn = function
      | Cst x -> x
      | Var _ -> failwith "Illegal polynomial"
      | Sum(p,q) -> fn p +. fn q
      | Sub(p,q) -> fn p -. fn q
      | Pro(p,q) -> fn p *. fn q
      | App(f,p) -> let p = List.map fn p in
                    B.eval f.bern (Array.of_list p)
      | Pow(p,n) -> pow (fn p) n
      | Fun(f,p) -> f.eval (fn p)
    in fn p

  let to_bernstein d vars p =
    let open B in
    let rec fn env = function
      | Cst x     -> cst d x
      | Var s     -> (try List.assoc s env with Not_found -> assert false)
      | Sum(p,q)  -> fn env p ++ fn env q
      | Sub(p,q)  -> fn env p -- fn env q
      | Pro(p,q)  -> fn env p ** fn env q
      | Pow(p,n)  -> pow (fn env p) n
      | App(p,qs) ->
         let env = List.combine p.vars (List.map (fn env) qs) in
         fn env p.poly
      | Fun _ as p -> cst d (eval_cst p)
    in
    let env = List.mapi (fun i v -> (v,[(var_power i d 1, R.one)])) vars in
    fn env p

  let mk name vars poly =
    let dim = List.length vars in
    let bern = to_bernstein dim vars poly in
    let (bern,h) = B.homogeneisation bern in
    let hdim = if h then dim + 1 else dim in
    let p = { name; vars; dim; poly; bern; hdim
            ; triangulation = []; edges = [] } in
    Hashtbl.add polys name p;
    p
end
