open Printing

let decomp_log = Debug.new_debug "decomposition" 'd'
let decomp_tst = decomp_log.tst
let decomp_log fmt = decomp_log.log fmt

let table_log = Debug.new_debug "table" 't'
let table_tst = table_log.tst
let table_log fmt = table_log.log fmt

module Make(R:Field.SPlus) = struct
  open R
  module Simp = Simplices.Make(R)
  module Poly = B
  open V
  open Simp
  open B

  (* type for the expected topologie *)
  type expected = Nothing (* expect anything *)
                | Int of int (* expect the given number of components *)
                | List of int list (* expect components with the given euler characteristics *)

  let all_dirs d =
    let res = ref [] in
    for i = 0 to d - 2 do
      for j = i+1 to d-1 do
        res := (i,j)::!res
      done
    done;
    !res

  let print_vpoly ch p =
    let first = ref true in
    List.iter (fun (l,c) ->
          begin
            if not !first then fprintf ch " + ";
            first := false;
            fprintf ch "%a " print_vector c;
            List.iteri (fun i e ->
                if e <> 0 then
                  if e > 1 then fprintf ch "X%d^%d " i e
                  else  fprintf ch "X%d " i) l;
          end) p

  type status =
    | Unknown
    | NonZero
    | NonDege
    | Removed

  type simplicies =
    { s : simplex
    ; m : matrix
    ; p : polynomial list
    ; dp : polynomial_v lazy_t list
    ; l : R.t array list
    ; c : R.t array
    ; mutable f : float
    ; mutable k : status
    ; suid : int array }

  let simplex_key s =
    let r = Array.map (fun v -> (v.uid, v.p)) s in
    Array.sort (fun (u1,_) (u2,_) -> compare u1 u2) r;
    let p1 = snd r.(0) in
    Array.map (fun (u,b) -> if b=p1 then u else -u) r

  let vertex_key v1 = v1.uid

  let edge_key v1 v2 =
    let i = v1.uid and j = v2.uid in
    let b = v1.p = v2.p in
    if i < j then (true,(i,j,b)) else (false,(j,i,b))

  let face_key s i =
    let r = ref [] in
    Array.iteri (fun j v -> if i <> j then r := (v.uid,v.p) :: !r) s;
    let r = List.sort (fun (i,_) (j,_) -> compare i j) !r in
    match r with
      | []       -> assert false
      | (i,p)::r -> (i, List.map (fun (j,q) -> (j, p = q)) r)

  let print_face_key ch (i, l) =
    fprintf ch "%d" i;
    List.iter (fun (j,b) -> fprintf ch ", %s%d" (if b then "+" else "-") j) l


  let h = one /. of_int 2

  let triangulation ?(expected=Nothing) p0 =
    let time0 = Unix.gettimeofday () in
    let dims = List.map dim p0 in
    let deg = List.map degree p0 in
    let dim = List.hd dims in
    if not (List.for_all ((=) dim) dims) then failwith "inhomogeneous equations";
    let sdim = dim - List.length p0 in
    let dirs = all_dirs dim in
    let ls = quadrants dim in
    let s0 = to_matrix (List.hd ls) in
    let dp0 = List.map tgradient p0 in
    let n = List.length ls in
    let all = Hashtbl.create 1001 in
    let add s = Hashtbl.replace all s.suid s in
    let rm s  = Hashtbl.remove all s.suid in
    let by_edge = Hashtbl.create 1001 in
    let by_vertex = Hashtbl.create 1001 in
    let by_face = Hashtbl.create 1001 in
    let add_v s =
      for i = 0 to dim-1 do
        let key = s.s.(i).uid in
        let l = try Hashtbl.find by_vertex key with Not_found -> [] in
        Hashtbl.replace by_vertex key ((i,s)::l)
      done
    in
    let rm_v s =
      for i = 0 to dim-1 do
        let key = s.s.(i).uid in
        let l = try Hashtbl.find by_vertex key with Not_found -> [] in
        let l = List.filter (fun (_,s') -> s.suid <> s'.suid) l in
        if l = [] then Hashtbl.remove by_vertex key
        else Hashtbl.replace by_vertex key l
      done
    in

    let add_e s =
      List.iter (fun (i,j) ->
          let (r,key) = edge_key s.s.(i) s.s.(j) in
          let (i,j) = if r then (i,j) else (j,i) in
          let l = try Hashtbl.find by_edge key with Not_found -> [] in
          Hashtbl.replace by_edge key ((i,j,s)::l)) dirs
    in
    let rm_e s =
      List.iter (fun (i,j) ->
          let (_,key) = edge_key s.s.(i) s.s.(j) in
          let l = try Hashtbl.find by_edge key with Not_found -> assert false in
          let l = List.filter (fun (_,_,s') -> s.suid <> s'.suid) l in
          if l = [] then Hashtbl.remove by_edge key
          else Hashtbl.replace by_edge key l) dirs
    in

    let add_f s = if dim > 2 then
      Array.iteri (fun i _ ->
          let key = face_key s.s i in
          let l = try Hashtbl.find by_face key with Not_found -> [] in
          if table_tst () then
            begin
              table_log "add_f: simplex with key %a" print_face_key key;
              List.iter
                (fun (i,s) -> table_log "  %d %a" i print_simplex s.s) ((i,s)::l);
            end;
          assert (List.length l <= 1);
          Hashtbl.replace by_face key ((i,s)::l)) s.s
    in
    let rm_f s = if dim > 2 then
      Array.iteri (fun i _ ->
          let key = face_key s.s i in
          let l = try Hashtbl.find by_face key with Not_found -> assert false in
          let old = List.length l in
          assert (old <= 2);
          let l = List.filter (fun (_,s') -> s.suid <> s'.suid) l in
          assert (List.length l = old - 1);
          if l = [] then Hashtbl.remove by_face key
          else Hashtbl.replace by_face key l) s.s
    in
    (*let find_e s1 s2 =
      let (_,key) = edge_key s1 s2 in
      Hashtbl.find by_edge key
    in*)
    let rm_s s =
      decomp_log "remove %a" print_simplex s.s;
      assert (s.k <> Removed);
      s.k <- Removed; rm s; rm_v s; rm_e s; rm_f s;
    in
    let add_s s = add s; add_v s; add_e s; add_f s in

    let order s1 s2 = Stdlib.compare s2.f s1.f in

    let mk ?(f=Stdlib.(1.0 /. float_of_int n)) s =
      let m = to_matrix s in
      decomp_log "before center";
      let c = center m in
      decomp_log "after center";
      let p = List.map (fun p -> Poly.transform p s0 m) p0 in
      decomp_log "after transform";
      let l = List.map plane p in
      decomp_log "after plane";
      let dp = List.map (fun p -> lazy (tgradient p)) p in
      let s = { s; m; p; k = Unknown; c; l; dp; f; suid = simplex_key s } in
      decomp_log "make %a" print_simplex s.s;
      add_s s;
      s
    in

    let to_do = List.map (fun s -> mk s) ls in
    let to_do = ref (List.sort order to_do) in
    decomp_log "init simplicies done";
    let add_to_do l = to_do := List.merge order (List.sort order l) !to_do in
    let total = ref 0.0 in

    let recheck s =
      match s.k with
      | Unknown -> true
      | NonZero -> true
      | NonDege -> false
      | Removed -> assert false
    in

    let re_add acc s =
      if recheck s then acc else
        Stdlib.(s.k <- Unknown; total := !total -. s.f; s::acc)
    in

    let constant_sign p =
      let ap = ref true in
      let an = ref true in
      let nz = ref 0    in
      List.iter (fun (_,c) ->
          let t = cmp c zero in
          if t < 0 then ap := false;
          if t > 0 then an := false;
          if t = 0 then incr nz;
        ) p;
      (!an || !ap) && !nz <= sdim
    in

    let constant_sign' p =
      let ap = ref true in
      let an = ref true in
      let nz = ref 0    in
      List.iter (fun c ->
          let t = cmp c zero in
          if t < 0 then ap := false;
          if t > 0 then an := false;
          if t = 0 then incr nz;
        ) p;
      (!an || !ap) && !nz <= sdim
    in

    let sub dps is =
      List.map (fun dp ->
          let res = ref [] in
          List.iter (fun (m,v) ->
              try
                for i = 0 to dim-1 do
                  if m.(i) <> 0 && not is.(i) then raise Exit;
                done;
                res := v :: !res
              with Exit -> ()) dp;
          !res) dps
    in

    let all_gradients vs {s; m; l=l0} =
      let l = ref [] in
      Array.iteri (fun i x -> if x then l := i :: !l) vs;
      let l = !l in
      let ls = match l with
        | []  -> assert false
        | [i] ->
           let l = try Hashtbl.find by_vertex s.(i).uid
                   with Not_found -> assert false
           in
           let l = List.map (fun (i',s') ->
                       assert (s'.s.(i').uid = s.(i).uid);
                       (s'.s.(i').p <> s.(i).p, s')) l
           in
           l
        | i::j::_ ->
           let r, k = edge_key s.(i) s.(j) in
           let l =
             try Hashtbl.find by_edge k with Not_found -> assert false in
           let test (_,_,s') =
               try
                 Array.iteri (fun i b ->
                     if b && Array.for_all (fun v -> v.uid <> s.(i).uid) s'.s
                     then raise Exit) vs;
                 true
               with
                 Exit -> false
           in
           let l = List.filter test l in
           let l = List.map (fun (i',j',s') ->
                       let i',j' = if r then i',j' else j',i' in
                       assert (s'.s.(i').uid = s.(i).uid);
                       assert (s'.s.(j').uid = s.(j).uid);
                       (s'.s.(i').p <> s.(i).p, s')) l
           in
           l
      in
      let gd = ref (List.map (fun _ -> []) l0) in
      List.iter (fun (opp,{s=s';l}) ->
         let l0 =
           List.map2 (fun deg l ->
               if deg mod 2 <> 0 && opp then Array.map (~-.) l else l) deg l
         in
         let s2 =
           if opp then Array.init dim (fun i -> cev s' i)
           else Array.init dim (fun i -> vec s' i)
         in
         let l = List.map (fun l -> V.transform l s2 m) l0 in
         gd := List.map2 (fun l gd -> l :: gd) l !gd ;
        ) ls;
      !gd
    in

    let decision_face vs s =
      let p = sub s.p vs in
      let dp = sub (List.map Lazy.force s.dp) vs in
      if not (List.exists constant_sign' p) then
      let gd = all_gradients vs s in

      let rec fn points dps gds =
        match (dps, gds) with
        | [dp], [gd] ->
           let new_points = dp @ gd in
           if zih (new_points @ points) then raise Zih
        | dp::dps, gd::gds ->
           let new_points = dp @ gd in
           let opp_new = List.map opp new_points in
           fn (new_points @ points) dps gds;
           fn (opp_new @ points) dps gds
        | _ -> assert false
      in
      fn [] dp gd
    in


    let iter_facets gn dim =
      let vs = Array.make dim false in
      let rec fn i =
        if i >= dim then
          begin
            if Array.exists (fun b -> b) vs then
              gn vs
          end
        else
          begin
            vs.(i) <- false;
            fn (i+1);
            vs.(i) <- true;
            fn (i+1)
          end
      in
      fn 0
    in

    let decision s =
      if List.exists (Array.for_all (fun x -> x =. zero)) s.l then Unknown else
      if List.exists constant_sign s.p then NonZero else
      let fn vs = decision_face vs s in
      try iter_facets fn dim; NonDege with Zih -> Unknown
    in

    let visible_v s x =
      let d = x *.* s.c in
      (d >=. zero, abs d >. one +. of_float 1e-15)
    in

    let visible s x =
      let x = to_vec x in
      visible_v s x
    in

    let center s =
      let c0 = normalise s.c in
      if !Args.rmax = 0.0 then Simp.mk c0 true else
      let cos2 c =
        let s = c0 *.* c in
        s *. s
      in
      let _cos c = sqrt (cos2 c) in
      let sin2 c =
        let x = one -. cos2 c  in
        if x <. zero then zero else x
      in
      let sin c = sqrt (sin2 c) in
      let rmax = sin (to_vec s.s.(0)) *. of_float !Args.rmax in
      assert (rmax >. zero);
      let force sgn c dc ndc =
        let rc = sin c in
        assert (rc <=. rmax);
        assert (snd (visible_v s c));
        (sgn *. (rmax -. rc) /. ndc) **. dc
      in
      let eval c = List.fold_left (fun acc p ->
                        let x = eval p c in acc +. x *. x) zero p0
      in
      let eval_grad c = List.fold_left (fun acc p ->
                        let x = eval_grad p c in acc +++  x) (zero_v dim) dp0
      in
      let rec loop steps sgn fc c dc ndc qc lambda =
        (* printf "objectif: %a lambda: %a rc: %a r: %a r-rc: %a\n %a => %a\n %a\n%!"
          print objectif print lambda print rc print r print (r -. rc) print_vector c print fc
          print_vector s.l;*)
        if lambda <. of_float 1e-8 || steps > 1000 then (c,fc,qc,steps) else
          let force = force sgn c dc ndc in
          (*printf "force: %a (%a)\n%!" print_vector force print (norm force);*)
          let c' = normalise (comb one c lambda force) in
          let fc' = eval c' in
          let dc' = eval_grad c' in
          let ndc' = norm2 dc' in
          let qc' = fc' /. ndc' *. (rmax -. sin c') in
          let (b1,b2) = visible_v s c' in
          if qc' <=. qc || sin c' >= rmax || not b1 || not b2 then
            loop (steps + 1) sgn fc c dc ndc qc (lambda /. of_int 2)
          else
            loop (steps + 1) sgn fc' c' dc' ndc' qc' (min one (of_int 2 *. lambda))

      in
      let fc0 = eval c0 in
      let dc0 = eval_grad c0 in
      let ndc0 = norm2 dc0 in
      let qc0 = fc0 /. ndc0 *. (rmax -. sin c0) in
      let (c1,_,qc1,_) = loop 0 one fc0 c0 dc0 ndc0 qc0 one in
      let (c2,_,qc2,_) = loop 0 (-.one) fc0 c0 dc0 ndc0 qc0 one in
      let c = if abs qc1 >. abs qc2 then c1 else c2 in
      let (c,b) = if c.(dim-1) <. zero then (opp c, false) else (c, true) in
      Simp.mk c b
    in


    let ajoute s x =
      let (sg, v) = visible s x in
      assert ((v && sg) ||
        let x = to_vec x in
        let m = Array.map (fun p -> p --- x) s.m in
        let m' = Array.map (fun p -> p +++ x) s.m in
        printf "\nx: %a(%a) s:%a => %a\n%a => %a\n%a => %a\n%!"
          print_vector x print (norm2 x)
          print_matrix s.m print_vector (Array.map norm2 s.m)
          print_matrix m print (det m)
          print_matrix m' print (det m');
        false);
      assert (s.k = Unknown);
      rm_s s;
      decomp_log "adding center %a" print_vector (to_vec x);
      to_do := List.filter (fun s' -> s'.suid <> s.suid) !to_do;
      let rec rml acc k = function
        | [] -> (None, List.rev acc)
        | (_,_,k' as c)::l -> if k = k' then (Some c, List.rev_append acc l)
                              else rml (c::acc) k l
      in
      let faces =
        List.init (Array.length s.s) (fun i ->
            let k = face_key s.s i in (i,s,k))
      in
      let rec fn area acc l =
        decomp_log "%d+%d faces" (List.length l) (List.length acc);
        match l with
        | []       -> (acc,area)
        | (i,s,key as c)::l ->
           decomp_log "test face %d of %a\ntest with key %a"
             i print_simplex s.s print_face_key key;
           assert (s.k = Removed);
           let l0 = try Hashtbl.find by_face key with Not_found -> [] in
           let (sg,v)   = visible s  x in
           assert v;
           match l0 with
           | [(j,s')] ->
              decomp_log "next simplex tested is %a" print_simplex s'.s;
              let (sg',v') = visible s' x in
              let i0 = if i = 0 then 1 else 0 in
              let j0 = ref 0 in
              while s'.s.(!j0).uid <> s.s.(i0).uid && !j0 < dim do incr j0 done;
              let j0 = !j0 in
              assert (j0 < dim);
              if v' then
                begin
                  assert (dim > 2);
                  decomp_log "to remove";
                  assert (s.s.(i0).uid = s'.s.(j0).uid);
                  let good = (sg = sg') = (s.s.(i0).p = s'.s.(j0).p) in
                  let acc = ref acc in
                  let l   = ref l   in
                  if s'.k <> Unknown then total := Stdlib.(!total -. s'.f);
                  rm_s s';
                  to_do := List.filter (fun s -> s'.suid <> s.suid) !to_do;
                  Array.iteri (fun k _ ->
                      if k <> j then
                        begin
                          let key' = face_key s'.s k in
                          let (b,l')  = rml [] key' !l   in
                          let (b',_)  = rml [] key' !acc   in
                          assert (b' = None);
                          match b with
                          | None ->
                             decomp_log "adding face %d of %a" k print_simplex s'.s;
                             l := (k,s',key') :: l'
                          | Some(h,s'',_) ->
                             l := l';
                             let h0 = if h = 0 then 1 else 0 in
                             let j0 = ref 0 in
                             while s'.s.(!j0).uid <> s''.s.(h0).uid && !j0 < dim do incr j0 done;
                             let j0 = !j0 in
                             assert (s''.s.(h0).uid = s'.s.(j0).uid);
                             let (sg'',v'') = visible s'' x in
                             assert v'';
                             let good = (sg'' = sg') = (s''.s.(h0).p = s'.s.(j0).p) in
                             if not good then (
                               acc := (k,s',face_key s'.s k) :: (h,s'',face_key s''.s h)
                                      :: !acc);
                        end) s'.s;
                  if not good then (
                    acc := (j,s',face_key s'.s j) :: c :: !acc);
                  fn Stdlib.(area+.s'.f) !acc !l
                end
              else
                fn area (c::acc) l
           | _ ->
              decomp_log "len: %d for %a\n%!" (List.length l0) print_face_key key;
              assert false
      in
      let (hole,area) = if dim > 2 then fn s.f [] faces else (faces, s.f) in
      let area = Stdlib.(area /. float (List.length hole)) in
      if dim = 2 then assert (List.length hole = 2);
      let added =
        List.map (fun (i,s,_) ->
            let (sg,v) = visible s x in
            assert v;
            let s' = Array.mapi (fun j y -> if i = j then x else y) s.s in
            if not sg then s'.(i) <- ch_sg x;
            decomp_log "before mk";
            let r = mk ~f:area s' in (*
               let k = face_key s i in
               let l = try Hashtbl.find by_face k with Not_found -> [] in
               (match l with
                | [(_,s')] -> assert (snd (visible s' x))
                | _ -> assert false);
               assert false;*)
            decomp_log "after mk";
            r
          ) hole
      in
      let ok = ref true in
      Hashtbl.iter (fun k l -> if List.length l <> 2 then
        (ok := false; eprintf "len = %d for key %a\n%!"
                        (List.length l) print_face_key k)) by_face;
      assert !ok;
      let add_local acc s =
        List.fold_left (fun acc (i,j) ->
            let (_,key) = edge_key s.s.(i) s.s.(j) in
            let l = try Hashtbl.find by_edge key with Not_found -> assert false in
            List.fold_left (fun acc (_,_,s) -> re_add acc s) acc l) acc dirs
      in
      add_to_do (List.fold_left add_local added added);
      decomp_log "readd local done"
    in
(*
    let _do_triangle x =
      let in_triangle s =
        let m = s.m in
        let c = pcoord x m in
        Array.for_all (fun x -> x *. c.(0) >= zero) c
      in
      try
        Hashtbl.iter (fun _ l ->
            List.iter (fun (_,s) ->
                if in_triangle s then
                  begin
                    let save = !debug in
                    debug := true;
                    let b = decision s in
                    debug := save;
                    printf "found %b\n%!" (b <> Unknown);
                    raise Exit
                  end) l) by_face
      with
        Exit -> ()
    in
 *)
    let rec test () =
      match !to_do with
      | []   -> true
      | s::ls ->
         decomp_log "before decision";
         let d = decision s in
         decomp_log "after decision %b" (d <> Unknown);
         if d = Unknown then
           begin
             let x = center s in
             ajoute s x;
             false
           end
         else
           begin
             to_do := ls;
             s.k <- d; total := Stdlib.(!total +. s.f);
             test ()
           end
    in

    while not (test ()) do
(*      if dim = 3 then
        begin
          if !show then
            begin
              init ();
              clear_graph ();
              let l = Hashtbl.fold (fun _ s acc -> s :: acc) all [] in
              display 100.0 (0.,0.) l (fun s -> s.m) None;
            end;
          if !debug then ignore (input_line stdin);
        end;
 *)
      let x = match !to_do with
        | [] -> assert false
        | s::_ -> s.f
      in
      let time1 = Unix.gettimeofday () in
      let dt = Stdlib.(time1 -. time0) in
      let (hd,tail) = if Debug.has_debug () then "", "\n" else "\r", "     " in
      eprintf "%sto do:%.3f%% %06d worst:%.2e, time: %.1fs%s%!"
        hd Stdlib.(!total *. 100.0) (List.length !to_do) x dt tail;

    done;

    eprintf "\r%f%% %d\n%!" Stdlib.(!total *. 100.0) (List.length !to_do);

    (*check ();*)

    let components faces =
      let open UnionFind in
      let tbl = Hashtbl.create 1024 in
      let fn face =
        let s = new_uf [face] in
        Array.iter (fun v ->
            try let s' = Hashtbl.find tbl v.uid in
                union (@) s s'
            with Not_found ->
              Hashtbl.add tbl v.uid s) face
      in
      List.iter fn faces;
      let res = ref [] in
      Hashtbl.iter (fun _ s ->
          let x = find_data s in
          if not (List.memq x !res) then res := x :: !res) tbl;
      !res
    in

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
          try incr (fst (Hashtbl.find tbl key))
          with Not_found ->
            if (dim - (1 + List.length (snd key))) mod 2 = 0
            then incr res else decr res;
            Hashtbl.add tbl key (ref 1, face)
        in
        iter_facets gn dim
      in
      List.iter fn faces;
      (*match !dim0 with
      | Some dim ->
         (*Hashtbl.iter (fun (_,l) (c,f) ->
             printf "%d %d => %d %a\n%!" dim (dim - (1 + List.length l)) !c
                       print_simplex f
           )
         tbl;*)
         Hashtbl.iter (fun (_,l) (c,_) ->
             if List.length l = dim - 1 then assert (!c = 1);
             if List.length l = dim - 2 then assert (!c = 2))
           tbl;
      | None -> ()*);
      !res
    in

    (*
    let newton x =
      let f x = Array.of_list (List.map (fun p -> eval p x) p0) in
      let df x = Array.of_list (List.map (fun dp -> eval_grad dp x) dp0) in
      let rec loop x fx nfx =
        let m = df x in
        let dx = solve_cg (m **** transpose m) fx in
        let x' = x --- of_float 0.0001 **. (m **- dx) in
        let fx' = f x' in
        let nfx' = norm2 fx' in
        if nfx' <. nfx then loop x' fx' nfx' else x
      in
      let fx = f x in
      let nfx = norm2 fx in
      loop x fx nfx
    in

    let newtons faces =
      let tbl = Hashtbl.create 1024 in
      let fn x =
        try
          let y:vertex = Hashtbl.find tbl x.uid in
          if y.p <> x.p then ch_sg y else y
        with
          Not_found ->
          let y = Simp.mk (newton x.v) x.p in
          Hashtbl.add tbl x.uid y;
          y
      in
      List.map (Array.map fn) faces
    in
     *)

    let rm_edge edges i j s ks =
      let (_,k) = edge_key s.(i) s.(j) in
      let l = try Hashtbl.find edges k with Not_found -> assert false in
      let l = List.filter (fun (_,_,s') ->
                  simplex_key s' <> ks) l
      in
      if l = [] then Hashtbl.remove edges k
      else Hashtbl.replace edges k l
    in

    let add_edge edges i j s =
      let (_,k) = edge_key s.(i) s.(j) in
      let l = try Hashtbl.find edges k with Not_found -> [] in
      let l = (i,j,s) :: l in
      Hashtbl.replace edges k l
    in

    let rm_simplex dirs edges simplices s =
      let ks = simplex_key s in
      Hashtbl.remove simplices ks;
      List.iter (fun (i,j) -> rm_edge edges i j s ks) dirs
    in

    let add_simplex dirs edges simplices s l =
      let ks = simplex_key s in
      if not (Hashtbl.mem simplices ks) then
        begin
          Hashtbl.add simplices ks (s,l);
          List.iter (fun (i,j) -> add_edge edges i j s) dirs
        end
    in

    let edges = Hashtbl.create 1024 in
    let simplices = Hashtbl.create 1024 in

    let total = ref 0 in

    Hashtbl.iter (fun k ls ->
        let fn (i,j,s) =
          let k = simplex_key s.s in
          if not (Hashtbl.mem simplices k) then
            begin
              incr total;
              Hashtbl.add simplices k (s.s,s.l);
            end;
          (i,j,s.s)
        in
        Hashtbl.add edges k (List.map fn ls)) by_edge;

    let total = !total in

    let rec extract dim codim dirs edges simplices =
      let edge_value l =
        match l with
        | [] -> assert false
        | (i,j,s)::_ ->
(*           printf "testing %a %a\n%!" print_vector (to_vec s.(i))
             print_vector (to_vec s.(j));*)
           let k = simplex_key s in
           let (_,l) = try Hashtbl.find simplices k with Not_found -> assert false in
           match l with
           | [] -> assert false
           | v :: _ ->
              (s.(i), v.(i), s.(j), v.(j))
      in

      let split_edge k =
        let l = try Hashtbl.find edges k with Not_found -> assert false in
        let (si,xi,sj,xj) = edge_value l in
        if xi *. xj <. zero then
          begin
            let t = xj /. (xj -. xi) in
            let u = xi /. (xi -. xj) in
            assert (t >. zero);
            assert (u >. zero);
            let x0 = comb t (to_vec si) u (to_vec sj) in
            (*            printf "splitting: %a\n%!" print_vector x0;*)
            let x0 = Simp.mk x0 true in
            let fn (i,j,s) =
              let sign,t,u =
                if s.(i).uid = si.uid then (s.(i).p = si.p,t,u)
                else if s.(i).uid = sj.uid then (s.(i).p = sj.p,u,t)
                else assert false
              in
              let x0 = if sign then x0 else ch_sg x0 in
              let k = simplex_key s in
              let (_,l) = try Hashtbl.find simplices k with Not_found -> assert false in
              let s1 = Array.mapi (fun k x -> if i = k then x0 else x) s in
              let s2 = Array.mapi (fun k x -> if j = k then x0 else x) s in
              let l1 = List.mapi (fun k0 v ->
                           Array.mapi (fun k x ->
                               if k = i then
                                 if k0 = 0 then zero else t *. x +. u *. v.(j)
                               else
                                 x) v) l
              in
              let l2 = List.mapi (fun k0 v ->
                           Array.mapi (fun k x ->
                               if k = j then
                                 if k0 = 0 then zero else u *. x +. t *. v.(i)
                               else
                                 x) v) l
              in
(*              printf "old: %a, " print_simplex s;
              List.iter (fun v -> printf "%a " print_vector v) l;
              print_newline();*)
              rm_simplex dirs edges simplices s;
(*              printf "new: %a, " print_simplex s1;
              List.iter (fun v -> printf "%a " print_vector v) l1;
              print_newline();
              printf "new: %a, " print_simplex s2;
              List.iter (fun v -> printf "%a " print_vector v) l2;
              print_newline();*)
              add_simplex dirs edges simplices s1 l1;
              add_simplex dirs edges simplices s2 l2;
            in
            List.iter fn l;
          end
      in

      let ls = ref [] in
      Hashtbl.iter (fun k _ -> ls := k :: !ls) edges;
      List.iter split_edge !ls;

      let new_edges = Hashtbl.create 1024 in
      let new_simplices = Hashtbl.create 1024 in
      let new_dirs = all_dirs dim in

      let collect _ (s,l) =
        let (keep, l) = match l with
          | [] -> assert false
          | v::ls ->
             let l = ref [] in
             Array.iteri (fun i x -> if x =. zero then l := i::!l) v;
             (List.rev !l, ls)
        in
        let nb_keep = List.length keep in
        (*        printf "s: %a, nb_keep: %d %d\n%!" print_simplex s nb_keep dim;*)
        assert (nb_keep <= dim);
        if nb_keep = dim then
          begin
            let s = Array.of_list (List.map (fun i -> s.(i)) keep) in
            let l = List.map (fun v ->
                        Array.of_list (List.map (fun i -> v.(i)) keep)) l in
(*            printf "keep: %a, " print_simplex s;
            List.iter (fun v -> printf "%a " print_vector v) l;
            print_newline();*)
            add_simplex new_dirs new_edges new_simplices s l
          end
      in

      Hashtbl.iter collect simplices;

      let dim = dim - 1 in
      let codim = codim - 1 in
      if codim > 0 then
        begin
          extract dim codim new_dirs new_edges new_simplices
        end
      else
        begin
          let all = ref [] in
          Hashtbl.iter (fun _ (s,l) ->
              assert (l=[]);
              all := s :: !all) new_simplices;
          !all
        end
    in

    let codim = List.length p0 in
    let all = extract (dim-1) codim dirs edges simplices in
    let keep = List.length all in
    let time1 = Unix.gettimeofday () in
    let dt = Stdlib.(time1 -. time0) in
    printf "total: %d/%d, time: %fs, " keep total dt;
    print_zih_summary ();
    let cps = components all in
    let chr = List.map euler cps in
    printf "%d components %a\n%!" (List.length cps) print_int_list chr;
    begin
      match expected with
      | Nothing -> ()
      | Int n ->
         if List.length chr <> n then
           failwith
             (sprintf "wrong number of components: %d, expected %d"
                (List.length chr) n)
      | List l ->
         let l = List.sort compare l in
         let chr = List.sort compare chr in
         if  l <> chr then
           failwith
             (sprintf "wrong characteristics of components: %a, expected %a"
                print_int_list chr print_int_list l)

    end;

    let edges = Hashtbl.fold (fun _ l acc ->
                    match l with
                    | [] -> assert false
                    | (i,j,s)::_ -> let s = to_matrix s.s in [|s.(i); s.(j)|]::acc)
                  by_edge []
    in

    (List.map to_matrix all, edges)

end
