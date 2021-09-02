open Printing
open Pacomb
open Db

module Parse(R:Field.SPlus) = struct

  module P = Expr.Make(R)
  module B = R.B
  module H = HyperSurfaces.Make(R)
  module D = H.D

  open P

  type cmd =
    Let_poly of string * string list * polynomial
  | Let_rand of string * string list * polynomial
  | Let_surf of string * Args.parameters * string list * polynomial list
  | Display  of string list
  | For      of string * polynomial * polynomial * polynomial * cmd list
  | Stats    of int * polynomial list

  let rec run_cmd = function
    | Let_poly(name,vars0,p) ->
       let p = P.mk false name vars0 p in
       let vars = Array.of_list vars0 in
       printf "%a\n%!" (B.print_polynome ~vars) (to_bernstein p.dim vars0 p.poly)
    | Let_rand(name,vars0,deg) ->
       let deg = eval_cst deg in
       let dim = List.length vars0 in
       let p = B.random false (R.to_int deg) dim in
       let pb = of_bernstein vars0 p in
       let p = P.mk true name vars0 pb in
       let vars = Array.of_list vars0 in
       printf "%a\n%!" (B.print_polynome ~vars) (to_bernstein p.dim vars0 p.poly)
    | Let_surf(name, opts, vars, pols) ->
       let dim = List.length vars in
       let ps = B.homogeneise_many (List.map (to_bernstein dim vars) pols) in
       let (ts, es, dim, topo, safe) =
         H.triangulation opts ps
       in
       if safe && !Args.dbname <> None then
         begin
           let rand p = match p with
             | App(p,_) -> p.rand | _ -> false
           in
           let fn p = P.mk (rand p) "" vars p in
           let pds = List.map fn pols in
           let pds = List.map (fun p -> ((p.vars, p.poly), p.deg, p.rand)) pds in
           let nbc = List.length topo in
           let topo_s = Topology.to_string topo in
           let rec pr_poly () (vars, p) = P.to_str pid vars p
           and pid (p:P.poly_rec) =
             let pid = Db.insert_polynomial pr_poly (p.vars, p.poly) p.deg p.dim p.rand in
             sprintf "P%Ld" pid
           in
           Db.insert_variety pr_poly pds dim nbc topo_s;
           printf "variety inserted in database\n%!";
         end;
       let os =
         if ts <> [] then
           begin
             let dim = Array.length (List.hd ts) in
             if dim = 1 then
               [D.mk_points_from_polyhedron name ts]
             else if dim = 2 then
               [D.mk_lines_from_polyhedron ~lwidth:2.0 name ts]
             else if dim = 3 then
               [D.mk_triangles_from_polyhedron name ts]
             else []
           end
         else []
       in
       let e_name = name ^ "__t" in
       let _os =
         if es <> [] then
           D.mk_lines_from_polyhedron e_name ~color:[|0.0;1.0;0.0;1.0|] es::os
         else os
       in
       ()
    | Display(names) ->
       Display.display names;
       if not (!Args.cont) then Display.wait ()
    | For(name,first,last,step,cmds) ->
       let first = eval_cst first in
       let last = eval_cst last in
       let step = eval_cst step in
       let open R in
       let i = ref first in
       while (!i <=. last) do
         let _ = P.mk false name [] (Cst !i) in
         List.iter run_cmd cmds;
         P.rm name;
         i := !i +. step;
       done
    | Stats(dim,degs) ->
       if !Args.dbname <> None then
         begin
           printf "stats\n%!";
           let degs = List.map (fun p -> R.to_int (eval_cst p)) degs in
           Db.stats dim degs
         end

  let expand_short_surf names =
    let p name =
      try Hashtbl.find polys name
      with Not_found -> Lex.give_up ~msg:("unbound variable "^name) ()
    in
    let ps = List.map p names in
    let vars = (List.hd ps).vars in
    if not (List.for_all (fun p -> p.vars = vars) ps) then
      failwith "Illegal short syntax for zeros";
    let pvs = List.map (fun v -> Var v) vars in
    let ps = List.map (fun p -> App(p,pvs)) ps in
    (vars, ps)

  (** Parses a float in base 10. [".1"] is as ["0.1"]. *)
  let float_lit : R.t Lex.t =
    let f = fun s0 n0 ->
        let b = Buffer.create 2048 in
        let found_digit = ref false in
        let rec fn s0 n0 =
          let (c,s,n) = Input.read s0 n0 in
          if (c >= '0' && c <= '9') then (
            found_digit := true;
            Buffer.add_char b c;
            fn s n)
          else (c,s,n,s0,n0)
        in
        let (c,s,n,s0,n0) =
          let (c,s,n) = Input.read s0 n0 in
          if c = '+' then fn s n
          else if c = '-' then (Buffer.add_char b c; fn s n)
          else if (c >= '0' && c <= '9') then (
            found_digit := true;
            Buffer.add_char b c;
            fn s n)
          else (c,s,n,s0,n0)
        in
        let (c,s,n,s0,n0) =
          if c <> '.' then (c,s,n,s0,n0) else
            (Buffer.add_char b c; fn s n)
        in
        if not !found_digit then Lex.give_up ();
        let (s0,n0) =
          if c <> 'E' && c <> 'e' then (s0,n0) else
            begin
              Buffer.add_char b c;
              let (c,s,n) =
                let (c,s,n as r) = Input.read s n in
                if c = '+' then
                  Input.read s n
                else if c = '-' then
                  (Buffer.add_char b c; Input.read s n)
                else r
              in
              if not (c >= '0' && c <= '9') then Lex.give_up ();
              Buffer.add_char b c;
              let (_,_,_,s,n) = fn s n in (s,n)
            end
        in
        (R.of_string (Buffer.contents b), s0, n0)
    in
    { n = "FLOAT"
    ; c = Charset.from_string "-+0-9."
    ; a = Lex.custom f
    ; f }

  let rec mul_cons n m l =
    if n <= 0 then l else mul_cons (n-1) m (m::l)

  let%parser option =
      "subd" "=" (p::INT) => (fun opt -> Args.{ opt with subd = p })
    ; "safe" "=" (p::FLOAT) => (fun opt -> Args.{ opt with safe = p })
    ; "delauney" "prec" "=" (p::FLOAT) => (fun opt -> Args.{ opt with dprec = p })
    ; "nb critical" "=" (p::INT) => (fun opt -> Args.{ opt with crit = p })
    ; "limit critical" "=" (p::FLOAT) => (fun opt -> Args.{ opt with crit_limit = p })
    ; "expected" "=" (l::Topology.parse) => (fun opt -> Args.{ opt with expected = l})

  let%parser rec options_aux =
      (p1::option) => (fun p -> p1 p)
    ; (p1::options_aux) ',' (p2::option) => (fun p -> p2 (p1 p))

  let%parser options =
      () => Args.default_parameters
    ; '[' (p::options_aux) ']' => (p Args.default_parameters)

  let%parser float = Grammar.term ~name:"float" float_lit

  let%parser ident = (v:: RE("[a-zA-Z_'][a-zA-Z0-9_']*"))           => v

  let%parser params =
      () => ([],())
    ; '(' (x::ident) (l:: ~* ( ',' (v::ident) => v )) ')' => (x::l, ())

  type p = Atom | Prod | Sum | Pow

  let string_of_prio = function
    | Atom -> "A"
    | Prod -> "P"
    | Sum  -> "S"
    | Pow  -> "W"

  let%parser fname =
    "cos" => { name = "cos"; eval = R.cos }

  (* for printing, we provide a function to convert priorities to string *)
  let poly vars =
    let%parser [@print_param string_of_prio] rec poly p =
        Atom < Pow < Prod < Sum
      ; (p=Atom) (x :: float)                      => Cst(x)
      ; (p=Atom) '(' (p::poly Sum) ')'             => p
      ; (p=Atom) (v::ident) (args::args)           => Ref(v,args)
      ; (p=Atom) "DIFF" "(" (p::poly Sum) "," (v::ident) ")"
                                                   => Der(p,v)
      ; (p=Pow) (x::poly Pow) '^' (n::INT)         => P.Pow(x, n)
      ; (p=Prod) '-' (x::poly Pow)                 =>
          (match x with Cst _ -> Lex.give_up ()
                       | _ -> Pro(Cst R.(-. one), x))
      ; (p=Prod) (x::poly Prod) '*' (y::poly Pow)  => Pro(x, y)
      ; (p=Prod) (x::poly Prod) '/' (y::float)     => Pro(Cst R.(one /. y),x)
      ; (p=Sum)  (x::poly Sum ) '+' (y::poly Prod) => P.Sum(x,y)
      ; (p=Sum)  (x::poly Sum ) '-' (y::poly Prod) => Sub(x,y)
      ; (f::fname) '(' (x::poly Sum) ')'           => Fun(f,x)

    and args =
        () => []
      ; '(' (x::poly Sum) (l:: ~* ( ',' (y::poly Sum) => y )) ')' => x::l
    in
    poly

  let%parser rec cmd =
      "let" (name::ident) ((vars,()) >: params) '=' (p::poly vars Sum) ';' =>
        Let_poly(name,vars,p)
    ; "let" (name::ident) ((vars,__) :: params) '=' "random" (deg::poly [] Sum) ';' =>
        Let_rand(name,vars,deg)
    ; "let" (name::ident)  '=' "zeros" ((vars,()) >: params) (opts::options)
        (pols:: ~+ (poly vars Sum)) ';' =>
        Let_surf(name, opts, vars, pols)
    ; "let" (name::ident) '=' "zeros" (opts::options)
        (names:: ~+ ident) ';' =>
        (let (vars, pols) = expand_short_surf names in
         Let_surf(name, opts, vars, pols))
    ; "display" (names :: ~+ ident) ';' =>
        Display(names)
    ; "for" (name::ident) "=" (first::poly [] Sum) "to" (last::poly [] Sum)
        (step:: ~? [Cst R.one] ("step" (x::poly [] Sum) => x))
        "do"
        (cmds :: ~+ cmd) "done" ';' =>
        For(name,first,last,step,cmds)
    ; "stats" (dim::INT) (degs :: ~+ (poly [] Sum)) ';' => Stats(dim,degs)

  let%parser cmds = (~* ((c::cmd) => run_cmd c)) => ()

end

let%parser main =
  match !Args.precision with
  | Args.Double ->
     let module P = Parse(Field.Float) in P.cmds
  | Args.Gmp n ->
     let module P = Parse(Field.Gmp) in
     Field.Gmp.set_prec n;
     P.cmds
