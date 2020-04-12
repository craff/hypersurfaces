
module Make(R:Field.S) = struct
  open R
  module Poly = Bernstein.Make(R)
  open Poly
  module V = Vector.Make(R)

  (** often need 1/2 *)
  let demi = one /. of_int 2

  (** Produces all vertices of the Newton polytope inside our simplex.
      This is simply all monomials *)
  let all_vertices dim degree =
    let res = ref [] in
    let rec fn acc dim degree =
      if dim = 1 then res := (degree::acc)::!res else
        for i = 0 to degree do
          fn (i::acc) (dim - 1) (degree-i)
        done;
    in
    fn [] dim degree;
    !res

  (** For simplicity, we need all monomials to be present in the polynomial *)
  (* FIXME: the can be improved by sorting the vertices first *)
  let complete p =
    let dim = dim p in
    let degree = degree p in
    let l = all_vertices dim degree in
    let res = ref p in
    List.iter (fun l -> if not (List.exists (fun (l',_) -> l = l') p) then res := (l,zero)::!res) l;
    List.sort (fun (l1,_) (l2,_) -> compare l2 l1) !res


  type vertex = { v : V.vector; p : bool; uid : int }

  let ch_sg e = { e with p = not e.p }

  let to_vec v =
    if v.p then v.v else Array.map (~-.) v.v

  let print_vertex ch v = V.print_vector ch (to_vec v)

  let mk =
    let c = ref 0 in
    (fun v p -> c := !c + 1; let uid = !c in { v; p; uid })

  type simplex = vertex array
  (** A simplex is represented by the coordinates of all its vertices.
      The boolen is a sign to share vertices with opposite sign.
      Sign matters if we want barycentrics coefficients to identify
      point "inside the simplex". The projective line has therefore
      two simplex with coordinates
      (0, 1) (1, 0) -> les points positifs
      (0, 1) (-1, 0) -> les points avec deux signes différents.
      Remarque: la derniere coordonnées sera toujours positive.
  *)

  let vec s i = to_vec s.(i)

  let cev s i =
    let e = s.(i) in
    if e.p then Array.map (~-.) e.v else e.v

  let to_matrix ?(opp=false) s : V.matrix =  Array.init (Array.length s) (fun i -> vec s i)

  let print_simplex ch s =
    let pr ch v =
      let sg = if v.p then "+" else "-" in
      Printf.fprintf ch "%s%a" sg V.print_vector v.v
    in
    V.print_array pr ch s

  let pos s i = s.(i).p
  let neg s i = not (pos s i)

  type quadrant = t list
  (** a quadrant is represented by a list with -1 and 1, ending with a 1,
      and whose size in the dimension. This list gives the sign of each variable.
      The list starts with a 1 because we are in the projective space and we can
      multiply by -1 *)

  let var dim i =
    Array.init dim (fun j -> if i = j then one else zero)

  (** Take a polynomials and returns a list of tuples (s,q) which gives
      the writing of p in each simplex, giving a complete decomposition of
      the projective space of dimension n (therefore 2^(n-1) simplices,
      if n is the dimension, that is the number of variables. *)
  let quadrants (dim:int) : simplex list =
    (* the identity matrix *)
    let q0 = Array.init dim (fun i -> mk (var dim i) true) in
    (* iterates fn on all quadrant *)
    let rec gn acc q i =
      if i < 0  then q::acc
      else
        begin
          let q' = Array.copy q in
          q'.(i) <- ch_sg q'.(i);
          gn (gn acc q' (i-1)) q (i-1)
        end
    in
    gn [] q0 (dim-2)

  (** midpoint *)
  let milieu a1 a2 =
    Array.mapi (fun i x -> demi *. (x +. a2.(i))) a1

  (** subdivise a polynomial, TODO comments *)
  let subdivise_half p t u i0 j0 =
    let d = dim p in
    let var i = Array.to_list (Array.init d (fun j -> if i = j then 1 else 0)) in
    (* Y = y/2, X = x + y/2 *)
    let values = Array.init d (fun i ->
                     if i = j0 then [(var j0, u)]
                     else if i = i0 then [(var j0,t)]++[(var i0,one)]
                     else [(var i,one)])
    in
    subst p (Array.to_list values)

  let subdivise p t u i0 j0 =
    (subdivise_half p t u i0 j0, subdivise_half p u t j0 i0)

  let select i l =
    let rec fn acc i = function
      | [] -> assert false
      | x::l -> if i = 0 then (x, List.rev_append acc l) else fn (x::acc) (i-1) l
    in (fn [] i l : int * int list)

  let insert i x l =
    let rec fn acc i l =
      if i = 0 then List.rev_append acc (x::l) else
        match l with
        | [] -> assert false
        | x::l -> fn (x::acc) (i-1) l
    in (fn [] i l: int list)

  let select2 i j l =
    assert (i < j);
    let y,l = select j l in
    let x,l = select i l in
    (l,(x,y))

  let insert2 i j (l,(x,y)) =
    assert (i < j);
    insert j y (insert i x l)

  let swap (x,y) = (y,x)


  let subdivise2 p t u i0 j0 =
    if i0 > j0 then swap (subdivise p u t j0 i0) else (
      (* on travaille à i+j fixé *)
      (*Printf.printf "coucou\n%!";*)
      let d = degree p in
      let res1 = ref [] in
      let res2 = ref [] in
      for i = 0 to d do
        (*Printf.printf "step %d\n%!" i;*)
        let q = List.filter (fun (l,c) -> List.nth l i0 + List.nth l j0 = i) p in
        (*print_polynome stdout q; print_newline ();*)
        let q = List.sort (fun ((l1,_), _) ((l2,_), _) -> compare l2 l1)
                          (List.map (fun (l,c) -> (select2 i0 j0 l, c)) q) in
        (*print_polynome' stdout q; print_newline ();*)
        let qs = List.fold_left (fun acc x ->
                     match acc, x with
                     | ((((l,_),_)::_ as first)::rest), (((l',_),_) as c) when l = l' ->
	                (c::first)::rest
                     | _, x -> [x]::acc) [] q
        in
        let qs = List.map List.rev qs in
        let hn q =
          (*Printf.printf "hn: ";
	  print_polynome' stdout q; print_newline ();*)
          let triangle = Array.make (i+1) [] in
          triangle.(0) <- q;
          for j = 1 to i do
            (*Printf.printf "hn(%d): " j;*)
	    let rec fn acc l = match l with
	      | ((l1,(x1,y1)),c1)::_ when y1 <> 0 && acc = [] ->
	         fn (((l1,(x1,y1-1)), u *. c1)::acc) l
	      | [(l1,(x1,y1)),c1] when x1 <> 0 ->
	         List.rev (((l1,(x1-1,y1)), t *. c1)::acc)
	      | ((l1,(x1,y1)),c1)::(((l2,(x2,y2)),c2)::_ as l') ->
  	         assert(x1 > x2);
	         assert(y1 < y2);
	         if x1 - 1 > x2  then
	           fn (((l2,(x2,y2-1)), u *. c2)::((l1,(x1-1,y1)), t *. c1)::acc) l'
	         else
	           fn (((l1,(x1-1,y1)), t*.c1+.u*.c2)::acc) l'
	      | _ -> List.rev acc
	    in
	    triangle.(j) <- fn [] triangle.(j-1);
            (*print_polynome' stdout triangle.(j); print_newline ();*)
          done;
          for j = 0 to i  do
	    (match triangle.(j) with
	     | ((l,(x,y)),c)::_ when y = 0 ->
	        res1 := (insert2 i0 j0 (l,(x,y+j)), c)::!res1
	     | _ -> ());
	    (match List.rev triangle.(j) with
	     | ((l,(x,y)),c)::_ when x = 0 ->
	        res2 := (insert2 i0 j0 (l,(x+j,y)), c)::!res2
	     | _ -> ());
          done;
        in
        List.iter hn qs
      done;
      let cmp (l,_) (l',_) = compare l' l in
      List.sort cmp !res1, List.sort cmp !res2)

  let debug = ref (Array.mem "-d" Sys.argv)
  let show = ref (Array.mem "-s" Sys.argv)

  exception Found

  let zero_in_hull m =
    let a2 =
      V.(zih (Array.map snd m))
    in
    (*let d = Array.length (snd m.(0)) in
    let rec fn f d n acc =
      if d < 0 then f acc else
        for i = d to n do
          fn f (d-1) (i-1) (i::acc)
        done
    in
    let z = Array.make d zero in
    let test_simplex l =
      let w = Array.of_list (List.map (fun i -> snd m.(i)) l) in
      try
        (*if !debug then Printf.eprintf "test simplex: %a\n%!"
                         V.print_matrix w;*)
        let v = V.bcoord z w in
        (*if !debug then Printf.eprintf "  => %a\n%!"
                         V.print_vector v;*)
        if Array.for_all (fun x -> cmp x zero >= 0) v then
          begin
            if !debug then
              begin
                Printf.eprintf "zero in hull: ";
                List.iter (fun i ->
                    Printf.eprintf "  %a %a\n%!" V.print_list (fst m.(i))
                      V.print_vector (snd m.(i))) l;
              end;
            raise Found
          end
      with
        Exit | Not_found -> ()
    in
    let a1 =
      try fn test_simplex d (Array.length m - 1) []; false
      with Found -> true
    in
    assert (a1 = a2 || (Printf.eprintf "%a\n%!" V.print_matrix (Array.map snd m); false));*)
    a2

end
