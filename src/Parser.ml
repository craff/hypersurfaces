open Pacomb

module Parse(R:Field.S) = struct

  open Bernstein.Make(R)
  module H = HyperSurfaces.Make(R)
  module D = Display.Make(R)

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

  let%parser float = Grammar.term ~name:"float" float_lit

  let%parser ident = (v:: RE("[a-zA-Z_'][a-zA-Z0-9_']*"))           => v

  let%parser params =
      () => ([],())
    ; '(' (x::ident) (l:: ~* ( ',' (v::ident) => v )) ')' => (x::l, ())

  type p = Atom | Prod | Sum

  let string_of_prio = function
    | Atom -> "A"
    | Prod -> "P"
    | Sum  -> "S"

  (* for printing, we provide a function to convert priorities to string *)
  let poly vars =
    let dim = List.length vars in
    let vars = List.mapi (fun i v -> (v,i)) vars in
    let%parser [@print_param string_of_prio] rec poly p =
        Atom < Prod < Sum
      ; (p=Atom) (x :: float)                      => cst dim x
      ; (p=Atom) '(' (p::poly Sum) ')'             => p
      ; (p=Atom) (v::ident)                        =>
          (let n = try List.assoc v vars
                   with Not_found -> Lex.give_up () in
           [(var_power n dim 1, R.one)])
      ; (p=Atom) (x::poly Atom) '^' (n::INT)       => pow x n
      ; (p=Prod) (x::poly Prod) '*' (y::poly Atom) => x ** y
      ; (p=Prod) (x::poly Prod) '/' (y::float)     => div_cst x y
      ; (p=Sum)  (x::poly Sum ) '+' (y::poly Prod) => x ++ y
      ; (p=Sum)  (x::poly Sum ) '-' (y::poly Prod) => x -- y
    in
    poly

  type poly_rec =
    { name : string
    ; dim : int
    ; hom : bool
    ; vars: string list
    ; poly : polynomial
    ; mutable triangulation : R.t Array.t Array.t list }

  let hdim p = if p.hom then p.dim - 1 else p.dim

  let polys = Hashtbl.create 101

  let%parser cmd =
      "let" (name::ident) ((vars,()) >: params) '=' (p::poly vars Sum) ';' =>
        (Hashtbl.add polys name
           { name; vars
           ; dim=List.length vars
           ; hom=homogeneous p
           ; poly=p
           ; triangulation = [] };
         Printf.printf "%a\n%!" print_polynome p)
    ; "zeros" (name::ident) ';' =>
        (try
           let p = Hashtbl.find polys name in
           let (ts, _, _) = H.triangulation (homogeneisation p.poly) in
           p.triangulation <- ts
         with Not_found -> Lex.give_up ())
    ; "display" (name::ident) ';' =>
        (try
           let p = Hashtbl.find polys name in
           let g = tgradient p.poly in
           let normal x = eval_grad g x in
           let o =
             if hdim p = 2 then
               D.mk_lines_from_polyhedron p.triangulation
             else if hdim p = 3 then
               D.mk_triangles_from_polyhedron p.triangulation normal
             else
               D.mk_lines_from_polyhedron []
           in
           Display.wait ();
           if hdim p = 2 then
             Display.rm_line_object o
           else if hdim p = 3 then
             Display.rm_triangle_object o
           else ();
         with Not_found -> Lex.give_up ())


    let%parser cmds = (~* cmd) => ()

 end


 let%parser main =
     (let module P = Parse(Field.Float) in P.cmds) => ()
   ; "precision" ((n,()) >: (n::INT => (n,())))
       (let module R = struct let prec=n end in
        let module P = Parse(Field.Gmp_R(R)) in
        P.cmds) => ()
