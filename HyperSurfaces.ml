let _ = Sys.catch_break true

module Make(R:Field.S) = struct
  open R
  module Simp = Simplices.Make(R)
  module Poly = Simp.Poly
  open Simp
  open Poly
  module Vec = Vector.Make(R)
  open Vec
  module D = Display.Make(R)
  open D

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
            if not !first then Printf.fprintf ch " + ";
            first := false;
            Printf.fprintf ch "%a " print_vector c;
            List.iteri (fun i e ->
                if e <> 0 then
                  if e > 1 then Printf.fprintf ch "X%d^%d " i e
                  else  Printf.fprintf ch "X%d " i) l;
          end) p

  type simplicies =
    { s : simplex
    ; p : polynomial
    ; dp : (int list * R.t array) list
    ; l : R.t array
    ; det : R.t
    ; mutable f : float
    ; mutable k : bool
    ; suid : int array }

  let simplex_key s =
    let r = Array.map (fun v -> (v.uid, v.p)) s in
    Array.sort (fun (u1,_) (u2,_) -> compare u1 u2) r;
    let p1 = snd r.(0) in
    Array.map (fun (u,b) -> if b=p1 then u else -u) r

  let vertex_key v1 = Simplices.(v1.uid)

  let edge_key v1 v2 =
    let i = v1.uid and j = v2.uid in
    let b = v1.p = v2.p in
    if i < j then (true,(i,j,b)) else (false,(j,i,b))

  let decision tbl deg dim {s; p; l=l0} =
    let ap = ref true in
    let an = ref true in
    List.iter (fun (_,c) ->
        let t = cmp c zero in
        if t < 0 then ap := false;
        if t > 0 then an := false) p;
    (not !ap && not !an &&
    let gd =
      let s1 = to_matrix s in
      let gd = ref (tgradient p) in
      Array.iteri (fun i (v:vertex) ->
          let key = vertex_key v in
          let ls = try Hashtbl.find tbl key with Not_found -> assert false in
          List.iter (fun (i',{s=s';l}) ->
              assert (s.(i).uid = s'.(i').uid);
              let opp = s.(i).p <> s'.(i').p in
              let l0 = if deg mod 2 <> 0 && opp then Array.map (~-.) l else l in
              let s2 =
                if opp then Array.init dim (fun i -> cev s' i)
                       else Array.init dim (fun i -> vec s' i)
              in
              let l = transform l0 s2 s1 in
              if not (List.exists (fun (_,v) ->
                          let r = ref true in
                          Array.iteri (fun i x -> r := !r && x =. l.(i)) v;
                          !r
                        ) !gd) then
                gd := (var_power i dim (deg-1),l) :: !gd)
            ls) s;
      Array.of_list !gd
    in
    if !debug then Printf.eprintf "test for %d points for\n %a %a\n%!" (Array.length gd)
      print_simplex s print_polynome p;
    if !debug then Array.iter (fun (l,v) -> Printf.eprintf " %a %a\n%!"
                                              print_list l print_vector v) gd;
    zero_in_hull gd)

  let h = one /. of_int 2

  let triangulation p0 =
    let dim = dim p0 in
    let deg = degree p0 in
    let dirs = all_dirs dim in
    let p0 = complete p0 in
    let ls = quadrants dim in
    let s0 = List.hd ls in
    let n = List.length ls in
    let all = Hashtbl.create 1001 in
    let by_vertex = Hashtbl.create 1001 in
    let add s = Hashtbl.replace all s.suid s in
    let rm s  = Hashtbl.remove all s.suid in
    let add_v s =
      Array.iteri (fun i v ->
          let key = vertex_key v in
          let l = try Hashtbl.find by_vertex key with Not_found -> [] in
          Hashtbl.replace by_vertex key ((i,s)::l)) s.s
    in
    let rm_v s =
      Array.iter (fun v ->
          let key = vertex_key v in
          let l = try Hashtbl.find by_vertex key with Not_found -> assert false in
          let l = List.filter (fun (_,s') -> s.suid <> s'.suid) l in
          if l = [] then Hashtbl.remove by_vertex key
          else Hashtbl.replace by_vertex key l) s.s
    in
    let find_v v =
      let key = vertex_key v in
      Hashtbl.find by_vertex key
    in
    let by_edge = Hashtbl.create 1001 in
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
    (*let find_e s1 s2 =
      let (_,key) = edge_key s1 s2 in
      Hashtbl.find by_edge key
    in*)
    let rm_s s = rm s; rm_v s; rm_e s in
    let add_s s = add s; add_v s; add_e s in

    let order s1 s2 = cmp s2.det s1.det in

    let face s i sg =
      let vs = ref [] in
      for j = 0 to dim - 1 do
        if i <> j then vs := (if sg then s.s.(j) else ch_sg s.s.(j)) :: !vs
      done;
      List.sort (fun v1 v2 -> compare v1.uid v2.uid) !vs
    in

    let conic s x =
      try
        let y = pcoord x (to_matrix s.s) in
        let sum = Array.fold_left (+.) zero y in
        (abs sum -. one, sum >. zero)
      with Not_found as e ->
        Printf.eprintf "\nnull det: %a\n%!" print_simplex s.s;
        raise e
    in

    let mk ?(f=Stdlib.(1.0 /. float_of_int n)) s =
      let p = Poly.transform p0 (to_matrix s0) (to_matrix s) in
      let dp = tgradient p in
      let s =
        { s; p; k = false; det = abs (det (to_matrix s))
        ; l = plane p; dp
        ; f; suid = simplex_key s }
      in
      if !debug then Printf.eprintf "make %a\n  %a\n%!" print_simplex s.s print_polynome s.p;
      add_s s;
      s
    in

    let to_do = List.map (fun s -> mk s) ls in
    let to_do = ref (List.sort order to_do) in
    let add_to_do l = to_do := List.merge order (List.sort order l) !to_do in
    let total = ref 0.0 in

    let re_add acc s =
      assert (not s.k);
      let fn acc s =
        Array.fold_left (fun acc v ->
            let ls = find_v v in
            List.fold_left (fun acc (_,s) ->
                if s.k then Stdlib.(s.k <- false; total := !total -. s.f; s::acc)
                else acc) acc ls
          ) acc s.s
      in
      fn acc s
    in

    let rec check ajoute moved x =
      let added = ref [] in
      let lost = ref 0.0 in
      let add n s =
        if List.exists (fun (_,s') -> s'.suid = s.suid) !added then
          begin
            added := List.filter (fun (_,s') -> s'.suid <> s.suid) !added;
            if !debug then Printf.eprintf "remove added %a\n%!" print_simplex s.s;
            rm_s s;
            if s.k then
              (s.k <- false; total := Stdlib.(!total -. s.f))
            else
              to_do := List.filter (fun s' -> s.suid <> s'.suid) !to_do;
          end
        else
          added := (n,s) :: !added
      in
      let fn s =
        if Array.exists (fun y -> x.uid = y.uid) s.s then
          add false s
        else
          begin
            let (c,sg) = conic s (to_vec x) in
            if c >=. zero then
              begin
                if !debug then Printf.eprintf "remove %a\n%!" print_simplex s.s;
                rm_s s;
                lost := Stdlib.(!lost +. s.f);
                if s.k then
                  (s.k <- false; total := Stdlib.(!total -. s.f))
                else
                  to_do := List.filter (fun s' -> s.suid <> s'.suid) !to_do;
                for i = 0 to dim - 1 do
                  let s' = Array.mapi (fun j y -> if i = j then x else
                                                    if sg then y else ch_sg y) s.s
                  in
                  add true (mk s')
                done
              end
          end
      in
      let ls =
        if ajoute then
          begin
            let ls = ref [] in
            Hashtbl.iter (fun _ x -> ls := x :: !ls) all;
            !ls
          end
        else
          List.map snd (find_v x)
      in
      List.iter fn ls;
      let nb = List.fold_left (fun nb (n,_) -> if n then nb +1 else nb) 0 !added in
      let f = Stdlib.(!lost /. float nb) in
      let l =
        List.fold_left (fun acc (n,s) ->
            if n then s.f <- f;
            if n || moved then
              begin
                Array.iter (fun x ->
                    let n = check false false x in
                    if ajoute then assert (n = 0)) s.s;
                re_add (s::acc) s
              end
            else acc) [] !added;
      in
      add_to_do l;
      List.length l
    in

    let ajoute x = ignore (check true false x) in (*
      let faces = ref ([] : Simp.vertex list list) in
      let f = ref 0.0 in
      let add_face f =
        if List.mem f !faces then
          faces := List.filter (fun f' -> f <> f') !faces
        else faces := f::!faces
      in
      let fn s =
        let (c, sg) = conic s (to_vec x) in
        if c >=. zero then
          begin
            if !debug then Printf.eprintf "remove %a\n%!" print_simplex s.s;
            rm_s s;
            if s.k then
              (s.k <- false; total := Stdlib.(!total -. s.f))
            else
              to_do := List.filter ((!=) s) !to_do;
            f := Stdlib.(!f +. s.f);
            for i = 0 to dim-1 do
              add_face (face s i sg)
            done;
          end;
      in
      Hashtbl.iter (fun _ -> fn) all;
      let f = Stdlib.(!f /. (float (List.length !faces))) in
      Printf.eprintf "new f: %e\n%!" f;
      let add acc vs =
        let s = Array.of_list (x::vs) in
        assert (det (to_matrix s) <>. zero);
        let s = mk ~f s in
        re_add (s::acc) s;
      in
      add_to_do (List.fold_left add [] !faces);
    in
                                     *)
    let center s =
      let best = ref [||] in
      let best_q = ref (~-. (of_int 2)) in
      let rec fn acc z d k =
        if d > 1 then
          for i = 1 to k-1 do
            fn (i::acc) (if i <> 0 then z+1 else z) (d - 1) (k-i)
          done
        else if z > 1 then begin
            let c = Array.of_list (k::acc) in
            let x = ref (zero_v dim) in
            Array.iteri (fun i n -> x := !x +++ of_int n **. vec s.s i) c;
            let x = V.normalise !x in
            let (q,_) = conic s x in
            if q >. !best_q then (best_q := q; best := x)
          end
      in
      fn [] 0 dim (4*dim);
      !best
    in

    let rec test () =
      match !to_do with
      | []   -> true
      | s::ls ->
         if decision by_vertex deg dim s then
           begin
             let x = center s in
             ajoute (Simp.mk x true);
             false
           end
         else
           begin
             to_do := ls;
             s.k <- true; total := Stdlib.(!total +. s.f);
             test ()
           end
    in

    while not (test ()) do
      if dim = 3 then
        begin
          let open Graphics in
          if !show then
            begin
              init ();
              clear_graph ();
              let l = Hashtbl.fold (fun _ s acc -> s :: acc) all [] in
              display 100.0 (0.,0.) l (fun s -> to_matrix s.s);
            end;
          if !debug then ignore (input_line stdin);
        end;
      let z =
        let open Stdlib in
        List.fold_left (fun acc s -> acc +. s.f) !total !to_do *. 100.0
      in
      let x = match !to_do with
        | [] -> assert false
        | s::_ -> s.f
      in
      if !debug then
        begin
          Printf.eprintf "%f%%/%f%% %d %e\n%!"
            Stdlib.(!total *. 100.0) z (List.length !to_do) x;
        end
      else
        Printf.eprintf "\r%f%%/%f%% %d %e                                                %!"
          Stdlib.(!total *. 100.0) z (List.length !to_do) x;
    done;

    Printf.eprintf "\r%f%% %d\n%!" Stdlib.(!total *. 100.0) (List.length !to_do);

    let polyhedrons = ref [] in
    let nb_keep = ref 0 in
    let nb_remove = ref 0 in
    let all = Hashtbl.fold (fun _ s acc -> s :: acc) all [] in
    List.iter (fun {s;p} ->
        let plane = List.combine (Array.to_list s) (Array.to_list (plane p)) in
        let pos,neg = List.partition (fun (p,x) -> x >. zero) plane in
        if !debug then
          begin
            Printf.eprintf "quadrant: %a\n%!" print_simplex s;
            Printf.eprintf "polynome: %a\n%!" print_polynome p;
            (* assert (len < dim); not true *)
          end;
        if pos = [] || neg = [] then
          begin
            if !debug then
              Printf.eprintf "keep nothin\n%!";
            incr nb_remove
          end
        else
          let ph = List.fold_left (fun acc (p,x) ->
                       List.fold_left (fun acc (q,y) ->
                           let open R in
                           Poly.digho p0 (one /. of_int 1_000_000) x (to_vec p) y (to_vec q)
                           (*let t = y /. (y -. x) in
                           let u = x /. (x -. y) in
                           comb t p u q*) :: acc) acc neg) [] pos
          in
          let ph = Array.of_list ph in
          if !debug then
            Printf.eprintf "keep polyedron: %a\n%!" print_matrix ph;
          polyhedrons := ph :: !polyhedrons;
          incr nb_keep) all;
    Printf.eprintf "total: %d, kept: %d, removed %d\n%!"
                   (!nb_keep + !nb_remove) !nb_keep !nb_remove;
    (*List.iter (fun ph ->
        Printf.eprintf "  %a\n%!" print_matrix ph) !polyhedrons;*)
    (!polyhedrons, List.map (fun s -> to_matrix s.s) all)

end
