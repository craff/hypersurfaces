open Format

exception Unbound of string
let unbound s = raise (Unbound s)

module Make(R:Field.SPlus) = struct

  open R

  type func = { name : string; eval : R.t -> R.t }

  type poly_rec =
    { name : string
    ; deg : int
    ; dim : int
    ; vars: string list
    ; poly : polynomial
    ; rand : bool
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
    | Der of polynomial * string
    | Fun of func * polynomial
    | Ref of string * polynomial list

  let polys : (string, poly_rec) Hashtbl.t = Hashtbl.create 101

  let to_str name_to_string vars p =
    let index v =
      let rec fn i l = match l with
        | [] -> assert false
        | x::l -> if x = v then i else fn (i+1) l
      in
      fn 0 vars
    in
    let rec to_str () =
      function
      | Cst x      -> (R.to_string x)
      | Var v      -> sprintf "x%d" (index v)
      | Pow (p,n)  -> sprintf "(%a)^%d" to_str p n
      | Sum (p,q)  -> sprintf "(%a+%a)" to_str p to_str q
      | Sub (p,q)  -> sprintf "(%a-%a)" to_str p to_str q
      | Pro (p,q)  -> sprintf "(%a*%a)" to_str p to_str q
      | App (f,ps) -> sprintf "%s(%a)" (name_to_string f) to_str_list ps
      | Fun (f,p)  -> sprintf "%s(%a)" f.name to_str p
      | Der (p,v)  -> sprintf "diff(%a,%s)" to_str p v
      | Ref _      -> assert false

    and to_str_list () = function
      | []   -> ""
      | [p]  -> to_str () p
      | p::l -> sprintf "%a,%a" to_str p to_str_list l
    in
    to_str () p

  let bind vars p =
    let rec bind = function
      | (Cst _ | Var _) as p -> p
      | Pow(p,n)             -> Pow(bind p, n)
      | Sum(p,q)             -> Sum(bind p, bind q)
      | Sub(p,q)             -> Sub(bind p, bind q)
      | Pro(p,q)             -> Pro(bind p, bind q)
      | App(p,qs)            -> App(p, List.map bind qs)
      | Fun(f,q)             -> Fun(f, bind q)
      | Der(p,v)             -> Der(bind p,v)
      | Ref(v,args)          ->
         try
           if args <> [] then raise Not_found;
           if not (List.mem v vars) then raise Not_found;
           Var v
         with Not_found -> try
             let p = Hashtbl.find polys v in
             let nb = List.length args in
             if p.dim <> nb then
               Pacomb.Lex.give_up ~msg:("bad arity for "^ v) ();
             App(p,List.map bind args)
           with Not_found ->
             Pacomb.Lex.give_up ~msg:("unbound variable "^v) ()
    in bind p

  let rec eval env p =
    let rec fn = function
      | Cst x -> x
      | Var v -> (try List.assoc v env with Not_found -> unbound v)
      | Sum(p,q) -> fn p +. fn q
      | Sub(p,q) -> fn p -. fn q
      | Pro(p,q) -> fn p *. fn q
      | App(f,l)-> let xs = List.map fn l in
                   let env = List.combine f.vars xs in
                   eval env f.poly
      | Pow(p,n) -> pow (fn p) n
      | Fun(f,p) -> f.eval (fn p)
      | Der _    -> failwith "diff in eval"
      | Ref(_,_) -> assert false (*
         try
           if l <> [] then raise Not_found;
           List.assoc v env
         with Not_found -> try
             let p = Hashtbl.find polys v in
             let nb = List.length l in
             if p.dim <> nb then
               Pacomb.Lex.give_up ~msg:("bad arity for "^ v) ();
             fn (App(p,l))
           with Not_found ->
             Pacomb.Lex.give_up ~msg:("unbound variable "^v) ()*)

    in fn p

  let eval_cst p = eval [] (bind [] p)

  let to_bernstein d vars p =
    let p = bind vars p in
    let open B in
    let rec fn env = function
      | Cst x     -> cst d x
      | Var s     -> (try List.assoc s env with Not_found -> unbound s)
      | Sum(p,q)  -> fn env p ++ fn env q
      | Sub(p,q)  -> fn env p -- fn env q
      | Pro(p,q)  -> fn env p ** fn env q
      | Pow(p,n)  -> pow (fn env p) n
      | Der(p,v)  -> let rec gn i = function
                       | [] -> unbound v
                       | (w,_)::l -> if v = w then i else gn (i+1) l
                     in
                     let v = gn 0 env in
                     B.partial (fn env p) v
      | App(p,qs) ->
         let env = List.combine p.vars (List.map (fn env) qs) in
         fn env p.poly
      | Fun _ as p -> cst d (eval_cst p)
      | Ref _    -> assert false
    in
    let env = List.mapi (fun i v -> (v,[(var_power i d 1, R.one)])) vars in
    fn env p

  let of_bernstein vars p =
    let fn (i,acc) n = (i+1,Pro(acc,Pow(Var(List.nth vars i),n))) in
    let gn (l,x) = snd (Array.fold_left fn (0, Cst (x *. B.multinomial l)) l) in
    let rec kn = function
      | [] -> Cst zero
      | [m] -> gn m
      | m::p -> Sum(gn m,kn p)
    in
    kn p

  let mk rand name vars poly =
    let dim = List.length vars in
    let poly = bind vars poly in
    let bern = to_bernstein dim vars poly in
    let deg = B.degree bern in
    let p = { name; vars; deg; dim; poly; rand
            ; triangulation = []; edges = [] } in
    if name <> "" then Hashtbl.add polys name p;
    p

  let rm name =
    Hashtbl.remove polys name

  let add_def (name, x) =
    let p = Cst (of_float x) in
    ignore (mk false name [] p)

  let _ = List.iter add_def !Args.defs
end
