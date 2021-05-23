open Printing
open Pacomb

module Parse(R:Field.SPlus) = struct

  module P = Expr.Make(R)
  module B = R.B
  module H = HyperSurfaces.Make(R)
  module D = H.D

  open P

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

  let%parser rec expected_aux =
    (n::INT) => [n]
  ; (n::INT) ',' (l::expected_aux) => n::l
  ; (n::INT) '*' (m::INT) => mul_cons n m []
  ; (n::INT) '*' (m::INT) ',' (l::expected_aux) => mul_cons n m l

  let%parser expected =
    ()  => Args.Anything
  ; (n::INT) => Args.Int n
  ; '(' ')' => Args.Int 0
  ; '(' (l::expected_aux) ')' => Args.List l

  let%parser option =
      "subd" "=" (p::INT) => (fun opt -> Args.{ opt with subd = p })
    ; "rmax" "=" (p::FLOAT) => (fun opt -> Args.{ opt with rmax = p })
    ; "delauney" "prec" "=" (p::FLOAT) => (fun opt -> Args.{ opt with dprec = p })
    ; "nb critical" "=" (p::INT) => (fun opt -> Args.{ opt with crit = p })
    ; "limit critical" "=" (p::FLOAT) => (fun opt -> Args.{ opt with crit_limit = p })
    ; "expected" "=" (l::expected) => (fun opt -> Args.{ opt with expected = l})

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
      ; (p=Atom) (v::ident) (args::args)           =>
          (try
             if args <> [] then raise Not_found;
             if not (List.mem v vars) then raise Not_found;
             Var v
           with Not_found -> try
             let p = Hashtbl.find polys v in
             let nb = List.length args in
             if p.dim <> nb then
               Lex.give_up ~msg:("bad arity for "^ v) ();
             App(p,args)
           with Not_found ->
              Lex.give_up ~msg:("unbound variable "^v) ())

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

  let%parser cmd =
      "let" (name::ident) ((vars,()) >: params) '=' (p::poly vars Sum) ';' =>
        (let p = P.mk name vars p in
         let vars = Array.of_list (vars @ ["s"]) in
         printf "%a\n%!" (B.print_polynome ~vars) p.bern)
    ; "let" (name::ident) '=' "zeros" (opts::options)
                                 (names:: ~+ ident) ';' =>
        (let p name =
           try (Hashtbl.find polys name).bern
           with Not_found -> Lex.give_up ~msg:("unbound variable "^name) ()
         in
         let ps = List.map p names in
         let (ts, es) = H.triangulation opts ps in
         let os =
           if ts <> [] then
             begin
               let dim = Array.length (List.hd ts) in
               if dim = 1 then
                 [D.mk_points_from_polyhedron name ts]
               else if dim = 2 then
                 [D.mk_lines_from_polyhedron name ts]
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
         ())
     ; "display" (names :: ~+ ident) ';' =>
         (Display.display names;
          if not (!Args.cont) then Display.wait ())

  let%parser cmds = (~* cmd) => ()

end

let%parser main =
  (let module P = Parse(Field.Float) in P.cmds) => ()
  ; "precision" ((n,()) >: (n::INT => (n,()))) ';'
      (let module P = Parse(Field.Gmp) in
       Field.Gmp.set_prec n;
       P.cmds) => ()
