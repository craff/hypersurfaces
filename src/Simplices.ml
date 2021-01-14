
module Make(R:Field.SPlus) = struct
  open R

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

  let to_matrix s : V.matrix =  Array.init (Array.length s) (fun i -> vec s i)

  let print_simplex ch s =
    let pr ch v =
      let sg = if v.p then "+" else "-" in
      Printf.fprintf ch "%s%a(%d)" sg V.print_vector v.v v.uid
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

  let delauney_dim dim m =
    let open V in
    let m = Array.of_list m in
    assert (Array.length m > dim);
    let base = Array.map to_vec m in
    Printf.printf "delauney_dim: %d %a\n%!" dim print_matrix base;
    reorder (dim+1) base;
    Printf.printf "ccoucou Q\n%!";
    let base = Array.sub base 0 (dim+1) in
    Printf.printf "ccoucou S\n%!";
    let mc = Array.map (fun x -> pcoord (to_vec x) base, x) m in
    Printf.printf "ccoucou T\n%!";
    let test = Array.map (fun (v,x) -> norm2 (base **- v --- to_vec x)) mc in
    let mc = Array.map (fun (v,x) -> (normalise v, x)) mc in
    let mcp = Array.map fst mc in
    Printf.printf "mc: %a %a\n%!" print_matrix mcp print_vector test;
    let faces = delauney (Array.to_list mcp) in
    let mc = Array.to_list mc in
    Printf.printf "%d\n%!" (List.length faces);
    Printf.printf "result: %a\n%!" (fun ch l -> List.iter (fun m -> print_matrix ch m) l) faces;
    let faces = List.map (Array.map (fun x ->
                              try List.assoc x mc with Not_found -> assert false)) faces in
    Printf.printf "result: %a\n%!" (fun ch l -> List.iter (fun m -> print_simplex ch m) l) faces;
    faces

  module Test = struct
    let a = List.map (fun x -> mk (Array.map of_int x) true)
        [
          [|0;0;1|];
          [|1;1;1|];
          [|0;1;1|];
          [|1;0;1|];
        ]

    let _ = delauney_dim 2 a

    let a = List.map (fun x -> mk (Array.map of_float x) true)
        [
          [|0.;0.;1.|];
          [|0.5;0.5;1.|];
          [|0.;1.;1.|];
          [|1.;0.;1.|];
        ]

    let _ = delauney_dim 2 a

  end

end
