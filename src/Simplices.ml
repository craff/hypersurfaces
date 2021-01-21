open Printing

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
      The boolean is a sign to share vertices with opposite sign.
      Sign matters if we want barycentrics coefficients to identify
      point "inside the simplex". The projective line has therefore
      two simplex with coordinates
      (0, 1) (1, 0) -> positive points
      (0, 1) (-1, 0) -> point with opposite signs
      Convention: last coordinate always positive.
  *)

  let vec s i = to_vec s.(i)

  let cev s i =
    let e = s.(i) in
    if e.p then Array.map (~-.) e.v else e.v

  let to_matrix s : V.matrix = Array.map to_vec s

  let print_simplex ch s =
    let pr ch v =
      let sg = if v.p then "+" else "-" in
      fprintf ch "%s%a(%d)" sg V.print_vector v.v v.uid
    in
    print_array pr ch s

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

end
