open Printing
open Topology
open Lib

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

  type 'a simplex =
    { s : vertex array
    ; m : V.m
    ; o : 'a
    ; mutable k : status
    ; suid : simplex_key }
  (** A simplex is represented by the coordinates of all its vertices. *)

  let print_vertex_array ch s =
    let pr ch v =
      let sg = if v.p then "+" else "-" in
      fprintf ch "%s%a(%d)" sg V.print_vector v.v v.uid
    in
    print_array pr ch s


  let print_simplex ch s =
    print_vertex_array ch s.s

  let simplex_key s =
    if Array.length s = 0 then [||] else
    let r = Array.map (fun v -> (v.uid, v.p)) s in
    Array.sort (fun (u1,_) (u2,_) -> compare u1 u2) r;
    for i = 0 to Array.length s - 2 do
      assert (fst r.(i) <> fst r.(i+1)
              || (printf "bad: %a\n%!" print_vertex_array s; false));
    done;
    let p1 = snd r.(0) in
    Array.map (fun (u,b) -> if b=p1 then u else -u) r

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
      | []       -> (0, [])
      | (i,p)::r -> (i, List.map (fun (j,q) -> (j, p = q)) r)

  let facet_key s vs =
    let r = ref [] in
    Array.iteri (fun j v -> if vs.(j) then r := (v.uid,v.p) :: !r) s;
    let r = List.sort (fun (i,_) (j,_) -> compare i j) !r in
    match r with
      | []       -> (0, [])
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

  let map fn tr =
    let all = hashtbl_map (fun s -> { s with o = fn s.o }) tr.all
    in
    let update s = try Hashtbl.find all s.suid with Not_found -> assert false in
    let by_vertex = hashtbl_map (List.map (fun (n,s) -> (n, update s))) tr.by_vertex in
    let by_edge = hashtbl_map (List.map (fun (n,m,s) -> (n, m, update s))) tr.by_edge in
    let by_face = hashtbl_map (List.map (fun (n,s) -> (n, update s))) tr.by_face in
    { dim = tr.dim; dirs = tr.dirs; all; by_vertex; by_edge; by_face
    ; nb = tr.nb; has_v_tbl = tr.has_v_tbl; has_e_tbl = tr.has_e_tbl; has_f_tbl = tr.has_f_tbl }


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
    table_log "rm simplex %a" print_simplex s;
    (*      decomp_log "remove %a" print_simplex s.s;*)
      assert (s.k <> Removed);
      s.k <- Removed;
      t.nb <- t.nb - 1;
      rm_s t.all s;
      if t.has_v_tbl then rm_v t.dim t.by_vertex s;
      if t.has_e_tbl then rm_e t.dirs t.by_edge s;
      if t.has_f_tbl then rm_f t.dim t.by_face s

  let add t s =
    table_log "add simplex %a" print_simplex s;
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

  let sub_face_key face vs =
    let key = ref [] in
    Array.iter2 (fun b v -> if b then key := (v.uid, v.p) :: !key) vs face;
    let key = List.sort (fun (x,_) (y,_) -> compare x y) !key in
    match key with
    | [] -> assert false
    | (x,b)::ls -> (x, List.map (fun (y,b') -> (y,b=b')) ls)

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
        let key = sub_face_key face vs in
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

  exception Found of (vertex * vertex)

  let simplify faces =
    let dim = match faces with
      | face :: _ -> Array.length face
      | [] -> 0
    in
    let trs = empty_triangulation dim in
    List.iter (fun f -> add trs (mks () f)) faces;
    let ok_edge (u1,u2,_ as k) =
      printf "testing %a\n%!" print_edge_key k;
      let faces = try Hashtbl.find trs.by_edge k with Not_found -> assert false in
      let ok_face (i,j,s) =
        printf "testing %a\n%!" print_face_key (face_key s.s i);
        let f1 = try Hashtbl.find trs.by_face (face_key s.s i)
                 with Not_found -> assert false in
        let s1 = match f1 with
          | [(i1,s1);(i2,s2)] ->
             if s1.suid = s.suid then s2 else s1
          | _ -> assert false
        in
        printf "testing %a\n%!" print_face_key (face_key s.s j);
        let f2 = try Hashtbl.find trs.by_face (face_key s.s j)
                 with Not_found -> assert false in
        let s2 = match f2 with
          | [(_,s1);(_,s2)] -> if s1.suid = s.suid then s2 else s1
          | _ -> assert false
        in
        assert (Array.exists (fun v -> v.uid = u2) s1.s);
        assert (Array.exists (fun v -> v.uid = u1) s2.s);
        Array.exists (fun v ->
            v.uid <> u2 && v.uid <> u1 &&
              Array.for_all (fun w -> w.uid <> v.uid)
                s2.s) s1.s
      in
      List.for_all ok_face faces
    in
    let find_simplification () =
      try
        Hashtbl.iter (fun (u1,u2,p as k) ls ->
            let b1 = try ok_edge k with Not_found -> assert false in
            let b2 = try ignore (Hashtbl.find trs.by_edge (u1,u2,not p));
                         false
                     with Not_found -> true
            in
            if b1 && b2 then
              let e =
                match ls with
                | [] -> assert false
                | (i,j,s) :: _ ->
                   assert (s.s.(i).uid = u1);
                   assert (s.s.(j).uid = u2);
                   assert (if p then s.s.(i).p = s.s.(j).p else
                             s.s.(i).p = not s.s.(j).p);
                   (s.s.(i), s.s.(j))
              in
              raise (Found e)) trs.by_edge;
        raise Not_found
      with
        Found e -> e
    in
    let merge (v1, v2) =
      let (rev, (u1,u2,p as k)) = edge_key v1 v2 in
      let (v1, v2) = if rev then (v2,v1) else (v1,v2) in
      printf "remove faces\n%!";
      let faces = try Hashtbl.find trs.by_edge k with Not_found -> assert false in
      List.iter (fun (_,_,f) ->
          printf "remove %a\n%!" print_simplex f;
          rm trs f) faces;
      printf "update faces remove\n%!";
      let faces = Hashtbl.find trs.by_vertex v1.uid in
      let to_add = List.map (fun (i,f) ->
          let s = f.s in
          assert (s.(i).uid = v1.uid);
          printf "remove to replace %a\n%!" print_simplex f;
          rm trs f;
          let v2 = if (s.(i).p = v1.p) then v2 else ch_sg v2 in
          let s' = Array.mapi (fun j v -> if i = j then v2 else v) s in
          mks () s') faces
      in
      printf "update faces add\n%!";
      List.iter (fun s ->
          printf "add %a\n%!" print_simplex s;
          add trs s) to_add;
      printf "check\n%!";
      try ignore (Hashtbl.find trs.by_vertex v1.uid); assert false
      with Not_found -> ()

    in
    try
      while true do
        printf "TEST\n%!";
        let (v1,v2) as e = find_simplification () in
        printf "MERGE %d %d\n%!" v1.uid v2.uid;
        merge e
      done;
      assert false
    with Not_found ->
      Hashtbl.fold (fun _ x acc -> x.s::acc) trs.all []

  let betti faces =
    let dim = match faces with
      | face :: _ -> Array.length face
      | [] -> 0
    in
    (*let faces = simplify faces in*)
    let count = Array.make dim 0 in
    let tbls = Array.init dim (fun _ -> Hashtbl.create 1024) in

    printf "\nstarting betti\n%!";
    let rec fn codim face =
      assert (Array.length face + codim = dim);
      Array.sort (fun v1 v2 -> compare v1.uid v2.uid) face;
      for i = 0 to Array.length face - 2 do
        assert (face.(i).uid <> face.(i+1).uid);
      done;
      let key = simplex_key face in
      try Hashtbl.find tbls.(codim) key
      with Not_found ->
        let index = count.(codim) in
        count.(codim) <- count.(codim) + 1;
        if Array.length face > 1 then
          begin
            let rec gn s acc = function
              | [] -> ()
              | x::l ->
                 let sub_f = Array.of_list (List.rev_append acc l) in
                 let index',row' = fn (codim + 1) sub_f in
                 row' := (index,s) :: !row';
                 gn (-s) (x::acc) l
            in
            gn 1 [] (Array.to_list face);
          end;
        let r = (index, ref []) in
        Hashtbl.add tbls.(codim) key r;
        r
    in
    List.iter (fun f -> ignore (fn 0 f)) faces;
    printf "tables build\n%!";
    let mats = Array.init (dim-1) (fun codim ->
      let tbl = tbls.(codim+1) in
      let nbc = count.(codim) in
      let nbl = count.(codim+1) in
      let m = Array.make nbl Rank.End in
      Hashtbl.iter (fun _ (i,row) ->
          assert (i < nbl);
          m.(i) <-
            List.fold_left (fun acc (i,x) ->
                assert (x < nbc);
                Rank.cons i (Z.of_int x) acc) Rank.End
              (List.sort (fun (a,_) (b,_) -> compare b a) !row)) tbl;
      m)
    in
    (*Array.iter (printf "%a\n%!" print_int_matrix) mats;*)
    printf "count: %a %d\n%!" print_int_array count (Array.length mats);
    let ranks = Array.mapi
                  (fun i -> Rank.rank count.(i+1) count.(i)) mats
    in
    Array.iter (fun (k,i) -> printf "(%d,%d) " k i) ranks;
    print_newline ();
    let betti =
      if dim = 1 then [1] else
      let (_,last) = ranks.(dim-2) in
      let betti = ref [count.(dim - 1) - last] in
      for i = dim - 2 downto 1 do
        let (k,_) = ranks.(i) in
        let (_,r) = ranks.(i-1) in
        betti := (k-r)::!betti
      done;
      let (k0,_) = ranks.(0) in
      k0 :: !betti
    in
    let e  = alt_sum_array count in
    let e' = alt_sum betti in
    assert (e = e');
    betti


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
    let rec kn nbp k c l =
      if List.length l = dim - 1 then
        begin
          incr tot;
          let l = (k - c) :: l in
          let nbp = if k = c then nbp else nbp + 1 in
          if nbp > 1 then
            begin
              (*assert (in_simplex s c1);*)
              let c1 = app l in
              lm := c1 :: !lm
            end
        end
      else
        for i = 0 to k - c do
          let nbp = if i = 0 then nbp else nbp + 1 in
          kn nbp k (c+i) (i::l)
        done
    in
    kn 0 nb 0 [];
    (*printf "%d/%d\n%!" (List.length !lm) !tot;*)
    !lm

  let topology mode faces =

    let cps = components faces in

    let fn c =
      match mode with
      | Ask_Nbc   -> Any
      | Ask_Euler -> Euler(euler c)
      | Ask_Betti -> Betti(betti c)
    in

    let cps = List.sort compare_one (List.map fn cps) in

    let rec fn acc l = match acc, l with
      | ((t1,n1)::acc, t2::l) when t1 = t2 -> fn ((t1,n1+1)::acc) l
      | (_, t2::l) -> fn ((t2,1)::acc) l
      | (_, [])    -> List.rev acc
    in
    fn [] cps


end
