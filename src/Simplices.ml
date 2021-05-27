open Printing

let table_log = Debug.new_debug "table" 't'
let table_tst = table_log.tst
let table_log fmt = table_log.log fmt

module Make(R:Field.SPlus) = struct
  open R

  (** Our representation of vectors in the projective space comes with a sign,
     not changing the value (becaus eof the projective quotient), hence not
     changing the uid.  Sign is usefull to denote simplicies, or convex hull in
     general.

     For instance, the segment [A,B] is defined by { u A + v B, u + v = 1, 0 <
     u,v < 1 } Hence, changing the sign control which half of the projective
     line is denoted by the segment.  *)
  type vertex =
    { v : V.vector (** coordinates of the vector *)
    ; p : bool     (** true if positive *)
    ; uid : int    (** uid: positive (>0) integer *) }

  (** sign inversion *)
  let ch_sg e = { e with p = not e.p }

  (** get the coordinated *)
  let to_vec v = if v.p then v.v else V.opp v.v

  let print_vertex ch v = V.print_vector ch (to_vec v)

  (** constructor, convention: last coordinate always positive. *)
  let mkv =
    let c = ref 0 in
    (fun v ->
      let dim = Array.length v in
      let (v,p) = if v.(dim-1) <. zero then (V.opp v,false)
                  else (v,true) in
      c := !c + 1; let uid = !c in { v; p; uid })

  type status =
    | Active
    | Removed

  type simplex_key = int array

  let simplex_key s =
    let r = Array.map (fun v -> (v.uid, v.p)) s in
    Array.sort (fun (u1,_) (u2,_) -> compare u1 u2) r;
    let p1 = snd r.(0) in
    Array.map (fun (u,b) -> if b=p1 then u else -u) r

  type 'a simplex =
    { s : vertex array
    ; m : V.m
    ; o : 'a
    ; mutable k : status
    ; suid : simplex_key }
  (** A simplex is represented by the coordinates of all its vertices. *)

  let print_simplex ch s =
    let pr ch v =
      let sg = if v.p then "+" else "-" in
      fprintf ch "%s%a(%d)" sg V.print_vector v.v v.uid
    in
    print_array pr ch s.s

  let pos s i = s.s.(i).p
  let neg s i = not (pos s i)


  let mks data s =
    let m = Array.map to_vec s in
    let s = { s; m; suid = simplex_key s
            ; o = data; k = Active } in
    s

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
      if n is the dimension, that is the number of variables.

      This function returns a list of matrices, not a list of simplicies
   *)
  let quadrants (dim:int) : V.m list =
    (* the identity matrix *)
    let q0 = Array.init dim (fun i -> mkv (var dim i)) in
    (* iterates fn on all quadrant *)
    let rec gn acc q i =
      if i < 0  then Array.map to_vec q::acc
      else
        begin
          let q' = Array.copy q in
          q'.(i) <- ch_sg q'.(i);
          gn (gn acc q' (i-1)) q (i-1)
        end
    in
    gn [] q0 (dim-2)

  type vertex_key = int
  type edge_key = int * int * bool
  type face_key = int * (int * bool) list

  let vertex_key v1 = v1.uid

  let edge_key v1 v2 =
    let i = v1.uid and j = v2.uid in
    let b = v1.p = v2.p in
    if i < j then (true,(i,j,b)) else (false,(j,i,b))

  let print_edge_key ch (i,j,b) =
    fprintf ch "(%d,%d,%b)" i j b

  let face_key s i =
    let r = ref [] in
    Array.iteri (fun j v -> if i <> j then r := (v.uid,v.p) :: !r) s;
    let r = List.sort (fun (i,_) (j,_) -> compare i j) !r in
    match r with
      | []       -> assert false
      | (i,p)::r -> (i, List.map (fun (j,q) -> (j, p = q)) r)

  type 'a triangulation =
    { dim       : int
    ; dirs      : (int * int) list
    ; all       : (simplex_key, 'a simplex) Hashtbl.t
    ; by_vertex : (vertex_key , (int * 'a simplex) list) Hashtbl.t
    ; by_edge   : (edge_key   , (int * int * 'a simplex) list) Hashtbl.t
    ; by_face   : (face_key   , (int * 'a simplex) list) Hashtbl.t
    ; mutable nb : int
    ; has_v_tbl : bool
    ; has_e_tbl : bool
    ; has_f_tbl : bool
    }

  let all_dirs d =
    let res = ref [] in
    for i = 0 to d - 2 do
      for j = i+1 to d-1 do
        res := (i,j)::!res
      done
    done;
    !res

  let empty_triangulation ?(has_v_tbl=true) ?(has_e_tbl=true) ?(has_f_tbl=true) dim =
    { dim; dirs = all_dirs dim
    ; all = Hashtbl.create 1001
    ; by_edge = if has_e_tbl then Hashtbl.create 1001 else Hashtbl.create 0
    ; by_vertex = if has_v_tbl then Hashtbl.create 1001 else Hashtbl.create 0
    ; by_face = if has_f_tbl then Hashtbl.create 1001 else Hashtbl.create 0
    ; nb = 0; has_e_tbl; has_f_tbl; has_v_tbl
    }

  let add_s all s = Hashtbl.replace all s.suid s
  let rm_s all s  = Hashtbl.remove all s.suid

  let add_v dim by_vertex s =
    for i = 0 to dim-1 do
      let key = s.s.(i).uid in
      let l = try Hashtbl.find by_vertex key with Not_found -> [] in
      Hashtbl.replace by_vertex key ((i,s)::l)
    done
  let rm_v dim by_vertex s =
    for i = 0 to dim-1 do
      let key = s.s.(i).uid in
      let l = try Hashtbl.find by_vertex key with Not_found -> [] in
      let l = List.filter (fun (_,s') -> s.suid <> s'.suid) l in
      if l = [] then Hashtbl.remove by_vertex key
      else Hashtbl.replace by_vertex key l
    done

  let add_e dirs by_edge s =
    List.iter (fun (i,j) ->
        let (r,key) = edge_key s.s.(i) s.s.(j) in
        let (i,j) = if r then (i,j) else (j,i) in
        let l = try Hashtbl.find by_edge key with Not_found -> [] in
        Hashtbl.replace by_edge key ((i,j,s)::l)) dirs
  let rm_e dirs by_edge s =
    List.iter (fun (i,j) ->
        let (_,key) = edge_key s.s.(i) s.s.(j) in
        let l = try Hashtbl.find by_edge key with Not_found -> assert false in
        let l = List.filter (fun (_,_,s') -> s.suid <> s'.suid) l in
        if l = [] then Hashtbl.remove by_edge key
        else Hashtbl.replace by_edge key l) dirs

  let print_face_key ch (i, l) =
    fprintf ch "%d" i;
    List.iter (fun (j,b) -> fprintf ch ", %s%d" (if b then "+" else "-") j) l
  let add_f dim by_face s =
    if dim > 2 then
      Array.iteri (fun i _ ->
          let key = face_key s.s i in
          let l = try Hashtbl.find by_face key with Not_found -> [] in
          if table_tst () then
            begin
              table_log "add_f: simplex with key %a" print_face_key key;
              List.iter
                (fun (i,s) -> table_log "  %d %a" i print_simplex s) ((i,s)::l);
            end;
          assert (List.length l <= 1);
          Hashtbl.replace by_face key ((i,s)::l)) s.s
  let rm_f dim by_face s =
    if dim > 2 then
      Array.iteri (fun i _ ->
          let key = face_key s.s i in
          let l = try Hashtbl.find by_face key with Not_found -> assert false in
          let old = List.length l in
          assert (old <= 2);
          let l = List.filter (fun (_,s') -> s.suid <> s'.suid) l in
          assert (List.length l = old - 1);
          if l = [] then Hashtbl.remove by_face key
          else Hashtbl.replace by_face key l) s.s

  let rm t s =
    (*      decomp_log "remove %a" print_simplex s.s;*)
      assert (s.k <> Removed);
      s.k <- Removed;
      t.nb <- t.nb - 1;
      rm_s t.all s;
      if t.has_v_tbl then rm_v t.dim t.by_vertex s;
      if t.has_e_tbl then rm_e t.dirs t.by_edge s;
      if t.has_f_tbl then rm_f t.dim t.by_face s

  let add t s =
    t.nb <- t.nb + 1;
    add_s t.all s;
    if t.has_v_tbl then add_v t.dim t.by_vertex s;
    if t.has_e_tbl then add_e t.dirs t.by_edge s;
    if t.has_f_tbl then add_f t.dim t.by_face s

  let mks ?t o s =
    let s = mks o s in
    begin
      match t with
      | None -> ()
      | Some t -> add t s
    end;
    s

  let components trs =
    let open UnionFind in
    let tbl = Hashtbl.create 1024 in
    let fn _ face =
      let s = new_uf [face.s] in
      Array.iter (fun v ->
          try let s' = Hashtbl.find tbl v.uid in
              union (@) s s'
          with Not_found ->
            Hashtbl.add tbl v.uid s) face.s
    in
    Hashtbl.iter fn trs.all;
    let res = ref [] in
    Hashtbl.iter (fun _ s ->
        let x = find_data s in
        if not (List.memq x !res) then res := x :: !res) tbl;
    !res

  let iter_facets codim dim gn =
    let vs = Array.make dim false in
    let rec fn codim i =
      if i >= dim then
        begin
          if Array.exists (fun b -> b) vs then
            gn (Array.copy vs)
        end
      else
        begin
          match codim with
            None    ->
             vs.(i) <- false; fn codim (i+1);
             vs.(i) <- true; fn codim (i+1)
          | Some cd ->
             if cd > 0 then
               (vs.(i) <- false; fn (Some (cd-1)) (i+1));
             if cd < dim - i then
               (vs.(i) <- true; fn codim (i+1))
        end
    in
    fn codim 0

  let enum_facets codim dim =
    let r = ref [] in
    iter_facets codim dim (fun f -> r := f :: !r);
    !r

  let euler faces =
    let res = ref 0 in
    let tbl = Hashtbl.create 1024 in
    let dim0 = ref None in
    let fn face =
      let dim = match !dim0 with
        | None -> let d = Array.length face in dim0 := Some d; d
        | Some d -> assert (d = Array.length face); d
      in
      let gn vs =
        let key = ref [] in
        Array.iter2 (fun b v -> if b then key := (v.uid, v.p) :: !key) vs face;
        let key = List.sort (fun (x,_) (y,_) -> compare x y) !key in
        let key = match key with
          | [] -> assert false
          | (x,b)::ls -> (x, List.map (fun (y,b') -> (y,b=b')) ls)
        in
        try ignore (Hashtbl.find tbl key)
        with Not_found ->
          if (dim - (1 + List.length (snd key))) mod 2 = 0
          then incr res else decr res;
          Hashtbl.add tbl key ()
      in
      iter_facets None dim gn
    in
    List.iter fn faces;
    !res

  (** [pts_in_simplex fn m nb] find the local minima of then function [fn] for
     points in simplex [m] with barycentric coordinated (i_1/nb, ..., i_k/nb)
     with sum i_j = nb and 0 <= i_j <= k *)
  let pts_in_simplex (m:V.matrix) nb =
    let lm = ref [] in
    let dim = Array.length m in
    let tot = ref 0 in
    let app l =
      let (c1,_) =
        List.fold_left (fun (acc,j) i ->
            (V.comb one acc (of_int i) m.(j),j+1)) (V.zero_v dim,0) l
      in
      V.normalise c1
    in
    let rec kn k c l =
      if List.length l = dim - 1 then
        begin
          incr tot;
          let l = (k - c) :: l in
          (*assert (in_simplex s c1);*)
          let c1 = app l in
          lm := c1 :: !lm
        end
      else
        for i = 0 to k - c do
          kn k (c+i) (i::l)
        done
    in
    kn nb 0 [];
    (*printf "%d/%d\n%!" (List.length !lm) !tot;*)
    !lm

end
