
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


  type simplex = t array array
  (** A simplex is represented by the coordinates of all its vertices.
      The sign matters if we want barycentrics coefficients to identify
      point "inside the simplex". The projective line has therefore
      two simplex with coordinates
      (0, 1) (1, 0) -> les points positifs
      (0, 1) (-1, 0) -> les points avec deux signes différents.
      Remarque: la derniere coordonnées sera toujours positive.
  *)

  type quadrant = t list
  (** a quadrant is represented by a list with -1 and 1, ending with a 1,
      and whose size in the dimension. This list gives the sign of each variable.
      The list starts with a 1 because we are in the projective space and we can
      multiply by -1 *)

  (** Take a polynomials and returns a list of tuples (s,q) which gives
      the writing of p in each simplex, giving a complete decomposition of
      the projective space of dimension n (therefore 2^(n-1) simplices,
      if n is the dimension, that is the number of variables. *)
  let quadrants p =
    let dim = dim p in
    (* the identity matrix *)
    let rec fn quadrant p =
      let q = Array.of_list quadrant in
      let _M = Array.init
                 dim
                 (fun i -> Array.init
                             dim
                             (fun j -> if i = j then q.(i) else zero))
      in
      (* sign of the monomial in the given quadrant, product of the -1 that
         correspondsto odd power, compensate for the -1 in the point coordinates *)
      let sn l = List.fold_left2 (fun acc n s ->
                     if n mod 2 = 0 then acc else s *. acc) one l quadrant
      in
      let p = List.map (function (l,c) -> (l, sn l *. c)) p in
      (_M, p)
    in
    (* iterates fn on all quadrant *)
    let rec gn acc quadrant n =
      if n = 1 then fn (List.rev (one::quadrant)) p::acc
      else gn (gn acc (~-.one::quadrant) (n-1)) (one::quadrant) (n-1)
    in
    gn [] [] dim

  (** midpoint *)
  let milieu a1 a2 =
    Array.mapi (fun i x -> demi *. (x +. a2.(i))) a1


  (** subdivise a simplex in two, splitting the edge between
      vertices i and j *)
  let split s i j =
    assert (i <> j);
    let m = milieu s.(i) s.(j) in
    let s1 = Array.mapi (fun k x -> if k = j then m else x) s in
    let s2 = Array.mapi (fun k x -> if k = i then m else x) s in
    (s1, s2)

  (** subdivise a simplex in two, splitting the edge between
      vertices i and j, inverse matrix to recover the barycentric
      coordinates in the subdivision from the coordinates in the original simplex *)
  let isplit s i j =
    assert (i <> j);
    let s1 = Array.mapi (fun k x ->
                 if k = j then Array.map (fun x -> of_int 2 *. x) x
                 else if k = i then Array.mapi (fun k x -> x -. s.(j).(k)) x
                 else x) s in
    let s2 = Array.mapi (fun k x ->
                 if k = i then Array.map (fun x -> of_int 2 *. x) x
                 else if k = j then Array.mapi (fun k x -> x -. s.(i).(k)) x
                 else x) s in
    (s1, s2)

  (** subdivise a polynomial, TODO comments *)
  let subdivise_half p i0 j0 =
    let d = dim p in
    let var i = Array.to_list (Array.init d (fun j -> if i = j then 1 else 0)) in
    (* Y = y/2, X = x + y/2 *)
    let values = Array.init d (fun i ->
                     if i = j0 then [(var j0, demi)]
                     else if i = i0 then [(var j0,demi)]++[(var i0,one)]
                     else [(var i,one)])
    in
    subst p (Array.to_list values)

  let subdivise p i0 j0 =
    (subdivise_half p i0 j0, subdivise_half p j0 i0)

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


  let subdivise2 p i0 j0 =
    if i0 > j0 then swap (subdivise p j0 i0) else
      (* on travaille à i+j fixé *)
      let d = degree p in
      let res1 = ref [] in
      let res2 = ref [] in
      for i = 0 to d do
        let q = List.filter (fun (l,c) -> List.nth l i0 + List.nth l j0 = i) p in
        (*    print_polynome q;*)
        let q = List.sort (fun ((l1,_), _) ((l2,_), _) -> compare l2 l1)
                          (List.map (fun (l,c) -> (select2 i0 j0 l, c)) q) in
        (*    print_polynome' q;*)
        let qs = List.fold_left (fun acc x ->
                     match acc, x with
                     | ((((l,_),_)::_ as first)::rest), (((l',_),_) as c) when l = l' ->
	                (c::first)::rest
                     | _, x -> [x]::acc) [] q
        in
        let qs = List.map List.rev qs in
        let hn q =
          (*      Printf.printf "coucou %d\n%!" i;
	print_polynome' q;*)
          let triangle = Array.make (i+1) [] in
          triangle.(0) <- q;
          for j = 1 to i do
	    let rec fn acc l = match l with
	      | ((l1,(x1,y1)),c1)::_ when y1 <> 0 && acc = [] ->
	         fn (((l1,(x1,y1-1)), demi *. c1)::acc) l
	      | [(l1,(x1,y1)),c1] when x1 <> 0 ->
	         List.rev (((l1,(x1-1,y1)), demi *. c1)::acc)
	      | ((l1,(x1,y1)),c1)::(((l2,(x2,y2)),c2)::_ as l') ->
  	         assert(x1 > x2);
	         assert(y1 < y2);
	         if x1 - 1 > x2  then (
	           fn (((l2,(x2,y2-1)), demi *. c2)::((l1,(x1-1,y1)), demi *. c1)::acc) l')
	         else
	           fn (((l1,(x1-1,y1)),demi *. (c1+.c2))::acc) l'
	      | _ -> List.rev acc
	    in
	    triangle.(j) <- fn [] triangle.(j-1);
            (*	print_polynome' triangle.(j)*)
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
      List.sort cmp !res1, List.sort cmp !res2

  let debug = ref (try Sys.argv.(1) = "-d" with _ -> false)

  exception Found

  let zero_in_hull m =
    let d = Array.length (snd m.(0)) in
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
        if !debug then Printf.eprintf "test simplex: %a\n%!"
                         V.print_matrix w;
        let v = V.bcoord z w in
        if !debug then Printf.eprintf "  => %a\n%!"
                         V.print_vector v;
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
    try fn test_simplex d (Array.length m - 1) []; false
    with Found -> true

end
