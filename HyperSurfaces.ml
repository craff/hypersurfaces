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
    ; l : R.t array
    ; f : float
    ; mutable x : R.t
    ; mutable d : int * int
    ; mutable k : bool
    ; suid : int }

  let order s1 s2 =
    match cmp s2.x s1.x with
    | 0 -> compare s2.f s1.f
    | c -> c

  let vertex_key v1 = Simplices.(v1.uid)

  let edge_key v1 v2 =
    let i = v1.uid and j = v2.uid in
    let b = v1.p = v2.p in
    if i < j then (true,(i,j,b)) else (false,(j,i,b))

  let eval dirs dim deg ({s;p;l} as s0) =
    (*if !debug then Printf.eprintf "eval %a => %a\n%!" print_matrix s print_vector l0;*)
    let best = ref zero in
    let best_i = ref 0 in
    let best_j = ref 0 in
    let dp = tgradient p in
    let t = Array.init dim (fun i -> List.assoc (var_power i dim (deg-1)) dp) in
    try
      List.iter (fun (i,j) ->
          let x = dist2 (vec s i) (vec s j) in
          let y = t.(i) *.* t.(j) in
          let zi = Array.for_all (fun x -> cmp x zero = 0) t.(i) in
          let zj = Array.for_all (fun x -> cmp x zero = 0) t.(j) in
          if zi && zj then (best_i := i; best_j := j; raise Exit);
          let f = y *. y /. (t.(i) *.* t.(i)) /. (t.(j) *.* t.(j)) in
          if not zi && not zj then
            begin
              let z = x /. (f +. one) in
              if cmp z !best > 0 then (best := x; best_i := i; best_j := j)
            end) dirs;
      (*if !debug then Printf.eprintf "eval => %a (%d, %d)\n%!" print !best !best_i !best_j;*)
      s0.x <- !best;
      s0.d <- (!best_i,!best_j)
    with Exit ->
      s0.x <- of_int 1_000_000_000;
      s0.d <- (!best_i,!best_j)


  let decision tbl deg dim {s; d; p; l=l0} =
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
              if !debug then Printf.eprintf " %d %a at %a with %b => %a => %a\n%!"
                               i print_simplex s' print_vertex v opp
                               print_vector l0 print_vector l;
              if not (List.exists (fun (_,v) ->
                          let r = ref true in
                          Array.iteri (fun i x -> r := !r && cmp x l.(i) = 0) v;
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

  let _ = Printexc.record_backtrace true

  let triangulation p0 =
    let dim = dim p0 in
    let deg = degree p0 in
    let dirs = all_dirs dim in
    let open Stdlib in
    let p0 = complete p0 in
    let ls = quadrants p0 in
    let (s0,p00) = List.hd ls in
    assert (p0 = p00);
    let n = List.length ls in
    let all = Hashtbl.create 1001 in
    let by_vertex = Hashtbl.create 1001 in
    let add s = Hashtbl.add all s.suid s in
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
          let l = List.filter (fun (_,s') -> s != s') l in
          if l = [] then Hashtbl.remove by_vertex key
          else Hashtbl.replace by_vertex key l) s.s
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
          let l = List.filter (fun (_,_,s') -> s != s') l in
          if l = [] then Hashtbl.remove by_edge key
          else Hashtbl.replace by_edge key l) dirs
    in
    let find_e s1 s2 =
      let (_,key) = edge_key s1 s2 in
      Hashtbl.find by_edge key
    in
    let rm_s s = rm s; rm_v s; rm_e s in
    let add_s s = add s; add_v s; add_e s in
    let count = ref 0 in
    let mk ?(f=1.0 /. float_of_int n) ?(k=false) ?(add=true) s p =
      let s =
        { s; p; x=zero; d=(0,0); k
        ; l = plane p
        ; f; suid = !count }
      in
      incr count;
      eval dirs dim deg s;
      if add then add_s s;
      s
    in


    let to_do = List.map (fun (s,p) -> mk s p) ls in
    let to_do = ref (List.sort order to_do) in
    let add_to_do l = to_do := List.merge order (List.sort order l) !to_do in
    let total = ref 0.0 in
    let nb_keep = ref 0 in
    let nb_remove = ref 0 in

    let rec split_s ?tm s i j =
      let v1 = Array.init dim (fun k -> if i = k then one else zero) in
      let v2 = Array.init dim (fun k -> if j = k then one else zero) in
      let v = v1 --- v2 in
      let dp = gradient s.p in
      let f t =
        let u = R.(one -. t) in
        let x = comb t v1 u v2 in
        Array.map (fun p -> Poly.eval p x) dp *.* v
      in
      let first = (tm = None) in
      let (t,m,s1,s2) = split ?tm f s.s i j in
      let tm = (t,m) in
      let p1 = Poly.transform p0 (to_matrix s0) (to_matrix s1) in
      let p2 = Poly.transform p0 (to_matrix s0) (to_matrix s2) in
      if !debug then
        begin
          Printf.eprintf "quadrant: %a\n%!" print_simplex s.s;
          Printf.eprintf "polynome: %a\n%!" print_polynome s.p;
          Printf.eprintf "split (%d,%d)\n%!" i j;
          Printf.eprintf "quadrant(1): %a\n%!" print_simplex s1;
          Printf.eprintf "polynome (1): %a\n%!" print_polynome p1;
          Printf.eprintf "quadrant(2): %a\n%!" print_simplex s2;
          Printf.eprintf "polynome (2): %a\n%!" print_polynome p2;
        end;
      rm_s s;
      let f = s.f /. 2.0 in
      let s1 = mk ~f ~k:s.k s1 p1 in
      let s2 = mk ~f ~k:s.k s2 p2 in
      if first then
        begin
          let l = find_e s.s.(i) s.s.(j) in
          if dim = 3 then assert (List.length l = 1);
          List.iter (fun (i',j',s') ->
              if !debug then Printf.eprintf "quadrant to split: %d %d %a\n%!" i j print_simplex s'.s;
              let (i',j') =
                if s.s.(i).uid = s'.s.(i').uid && s.s.(j).uid = s'.s.(j').uid then (i',j')
                else if s.s.(i).uid = s'.s.(j').uid && s.s.(j).uid = s'.s.(i').uid then (j',i')
                else assert false
              in
              let same_sign = s.s.(i).p = s'.s.(i').p in
              assert (same_sign = (s.s.(j).p = s'.s.(j').p));
              let tm = if same_sign then tm else (t,{m with p = not (m.p)}) in
              split_s ~tm s' i' j') l;
          try ignore (find_e s.s.(i) s.s.(j)); assert false;
          with Not_found -> ()
        end;
      if not s.k then
        begin
          add_to_do [s1;s2];
          if not first then to_do := List.filter (fun s' -> s != s') !to_do
        end;
    in

    let rec test () =
      match !to_do with
      | []   -> true
      | s::ls ->
         try
           assert (not s.k);
           if dim <> 3 then raise Exit;
           List.iter (fun (i,j) ->
               let l = find_e s.s.(i) s.s.(j) in
               try
                 match l with
                 | [(i1,j1,s1);(i2,j2,s2)] ->
                    assert (s1 == s || s2 == s);
                    assert (s1.s.(i1).uid = s2.s.(i2).uid);
                    assert (s1.s.(j1).uid = s2.s.(j2).uid);
                    let k = List.find (fun k -> k <> i1 && k <> j1) [0;1;2] in
                    let l = List.find (fun k -> k <> i2 && k <> j2) [0;1;2] in
                    let (ss1,ss2) =
                      if s1.s.(i1).p = s2.s.(i2).p then
                        begin
                          assert (s1.s.(j1).p = s2.s.(j2).p);
                          ([|s1.s.(i1); s1.s.(k); s2.s.(l)|],
                           [|s1.s.(j1); s1.s.(k); s2.s.(l)|])
                        end
                      else
                        begin
                          assert (s1.s.(j1).p <> s2.s.(j2).p);
                          ([|s1.s.(i1); s1.s.(k); ch_sg s2.s.(l)|],
                           [|s1.s.(j1); s1.s.(k); ch_sg s2.s.(l)|])
                        end
                    in
                    if cmp R.(det (to_matrix ss1) *. det (to_matrix ss2)) zero >= 0 then
                      raise Exit;
                    let p1' = Poly.transform s1.p (to_matrix s1.s) (to_matrix ss1) in
                    let p2' = Poly.transform s1.p (to_matrix s1.s) (to_matrix ss2) in
                    let f = (s1.f +. s2.f) /. 2.0 in
                    let s1' = mk ~add:false ~f ss1 p1' in
                    let s2' = mk ~add:false ~f ss2 p2' in
                    if cmp R.(s1'.x +. s2'.x) R.(s1.x +. s2.x) >= 0 then raise Exit;
                    if s1.k then total := !total -. s1.f;
                    if s2.k then total := !total -. s2.f;
                    if !debug then
                      Printf.eprintf "transform %a %a: \n %a %a\n %a %a\n=>\n %a %a\n %a %a\n"
                        print (det (to_matrix ss1)) print (det (to_matrix ss2))
                        print_simplex s1.s print_polynome s1.p
                        print_simplex s2.s print_polynome s2.p
                        print_simplex ss1 print_polynome p1'
                        print_simplex ss2 print_polynome p2';
                    rm_s s1; rm_s s2; add_s s1'; add_s s2';
                    to_do := List.filter (fun s' -> s1 != s' && s2 != s') !to_do;
                    add_to_do [s1';s2'];
                    raise Found
                 | _       ->
                    Printf.eprintf "len: %d\n%!" (List.length l);
                    assert false
               with Exit -> ()) dirs;
           raise Exit
         with
         | Exit ->
            to_do := ls;
            if decision by_vertex deg dim s then
              begin
                let (i,j) = s.d in
                split_s s i j;
                false
              end
            else
              begin
                s.k <- true; total := !total +. s.f;
                test ()
              end
         | Found -> false
    in

    while not (test ()) do
      let x = match !to_do with
        | [] -> assert false
        | s::_ -> s.x
      in
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
      let z = List.fold_left (fun acc s -> acc +. s.f) !total !to_do *. 100.0 in
      if !debug then
        begin
          Printf.eprintf "%f%%/%f%% %d %e\n%!"
            (!total *. 100.0) z (List.length !to_do) (to_float x);
        end
      else
        Printf.eprintf "\r%f%%/%f%% %d %e                                                %!"
          (!total *. 100.0) z (List.length !to_do) (to_float x);
    done;

    Printf.eprintf "\r%f%% %d\n%!" (!total *. 100.0) (List.length !to_do);

    let polyhedrons = ref [] in
    let all = Hashtbl.fold (fun _ s acc -> s :: acc) all [] in
    List.iter (fun {s;p} ->
        let plane = List.combine (Array.to_list s) (Array.to_list (plane p)) in
        let pos,neg = List.partition (fun (p,x) -> cmp x zero > 0) plane in
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
