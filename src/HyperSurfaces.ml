open Args

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

  type status =
    | Unknown
    | NonZero
    | NonDege of R.t array

  type simplicies =
    { s : simplex
    ; p : polynomial
    ; dp : (int list * R.t array) list
    ; l : R.t array
    ; det : R.t
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
    Array.iteri (fun j v -> if i <> j then r := (v.uid,v.p) :: !r) s.s;
    let r = List.sort (fun (i,_) (j,_) -> compare i j) !r in
    match r with
      | []       -> assert false
      | (i,p)::r -> ((i, List.map (fun (j,q) -> (j, p = q)) r), p)

  let print_face_key ch (i, l) =
    Printf.fprintf ch "%d " i;
    List.iter (fun (j,b) -> Printf.fprintf ch ", %s%d" (if b then "+" else "-") j) l


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
    let add s = Hashtbl.replace all s.suid s in
    let rm s  = Hashtbl.remove all s.suid in
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
    let by_face = Hashtbl.create 1001 in

    let add_f s =
      Array.iteri (fun i _ ->
          let (key, b) = face_key s i in
          let l = try Hashtbl.find by_face key with Not_found -> [] in
          if List.length l > 1 then
            begin
              Printf.eprintf "%a\n%!" print_face_key key;
              List.iter
                (fun (i,_,s) -> Printf.eprintf "%d %a\n%!" i print_simplex s.s) ((i,b,s)::l)
            end;
          assert (List.length l <= 1);
          Hashtbl.replace by_face key ((i,b,s)::l)) s.s
    in
    let rm_f s =
      Array.iteri (fun i _ ->
          let (key, _) = face_key s i in
          let l = try Hashtbl.find by_face key with Not_found -> assert false in
          let old = List.length l in
          assert (old <= 2);
          let l = List.filter (fun (_,_,s') -> s.suid <> s'.suid) l in
          assert (List.length l = old - 1);
          if l = [] then Hashtbl.remove by_face key
          else Hashtbl.replace by_face key l) s.s
    in
    (*let find_e s1 s2 =
      let (_,key) = edge_key s1 s2 in
      Hashtbl.find by_edge key
    in*)
    let rm_s s =
      if !debug then Printf.eprintf "remove %a\n%!" print_simplex s.s;
      rm s; rm_e s; rm_f s;
    in
    let add_s s = add s; add_e s; add_f s in

    let order s1 s2 = Stdlib.compare s2.f s1.f in

    let mk ?(f=Stdlib.(1.0 /. float_of_int n)) s =
      let p = Poly.transform p0 (to_matrix s0) (to_matrix s) in
      let dp = tgradient p in
      let s =
        { s; p; k = Unknown; det = det (to_matrix s)
        ; l = plane p; dp
        ; f; suid = simplex_key s }
      in
      if !debug then Printf.eprintf "make %a\n  %a\n%!" print_simplex s.s print_polynome s.p;
      add_s s;
      s
    in

    let to_do = List.map (fun s -> mk s) ls in
    let to_do = ref (List.sort order to_do) in
    if !debug then Printf.eprintf "init simplicies done\n%!";
    let add_to_do l = to_do := List.merge order (List.sort order l) !to_do in
    let total = ref 0.0 in

    let all_gradients {s; p; l=l0; suid=uid}  =
      let s1 = to_matrix s in
      let eq v w =
        let r = ref true in
        Array.iteri (fun i x -> r := !r && x =. w.(i)) v;
        !r
      in
      let add l v = if List.exists (eq v) l then l else v :: l in
      let gd = ref (List.fold_left add [] (l0 :: List.map snd (tgradient p))) in
      List.iter (fun (i,j) ->
          let (r,key) = edge_key s.(i) s.(j) in
          let (i,j) = if r then (i,j) else (j,i) in
          let l = try Hashtbl.find by_edge key with Not_found -> assert false in
          assert (List.length l >= 2);
          List.iter (fun (i',j',{s=s';suid=uid';l}) ->
              if uid <> uid' then
                begin
                  assert (s.(i).uid = s'.(i').uid);
                  let opp = s.(i).p <> s'.(i').p in
                  let l0 = if deg mod 2 <> 0 && opp then Array.map (~-.) l else l in
                  let s2 =
                    if opp then Array.init dim (fun i -> cev s' i)
                    else Array.init dim (fun i -> vec s' i)
                  in
                  let l = transform l0 s2 s1 in
                  gd := add !gd l;
                end)
            l) dirs;
      Array.of_list !gd
    in

    let recheck s =
      match s.k with
      | Unknown   -> true
      | NonZero   -> true
      | NonDege v ->
         let gd = all_gradients s in
         Array.for_all (fun w -> w *.* v <. zero) gd
    in

    let re_add acc s =
      if recheck s then acc else
        Stdlib.(s.k <- Unknown; total := !total -. s.f; s::acc)
    in


    let decision s =
      let ap = ref true in
      let an = ref true in
      List.iter (fun (_,c) ->
          let t = cmp c zero in
          if t < 0 then ap := false;
          if t > 0 then an := false) s.p;
      if !an || !ap then NonZero else
        begin
          let gd = all_gradients s in
          if !debug then Printf.eprintf "test for %d points for\n %a %a\n%!" (Array.length gd)
                           print_simplex s.s print_polynome s.p;
          if !debug then Array.iter (fun v -> Printf.eprintf " %a\n%!"
                                                print_vector v) gd;
          match zih gd with Some v -> NonDege v | None ->Unknown
        end
    in

    let visible s b x =
      let x = to_vec x in
      let x = if b then x else opp x in
      let m = Array.map (fun p -> p --- x) (to_matrix s.s) in
      det m *. s.det <. zero
    in

    let center s =
      let c = V.normalise (center (to_matrix s.s)) in
      let c = Simp.mk c true in
      if visible s true c then c else ch_sg c
    in


    let ajoute s x =
      assert (visible s true x ||
        let x = to_vec x in
        let m = Array.map (fun p -> p --- x) (to_matrix s.s) in
        let m' = Array.map (fun p -> p +++ x) (to_matrix s.s) in
        Printf.printf "\n%a => %a\n%a => %a\n%a => %a\n%!"
          print_matrix (to_matrix s.s) print s.det
          print_matrix m print (det m)
          print_matrix m' print (det m');
        false);
      assert (s.k = Unknown);
      rm_s s;
      to_do := List.filter (fun s' -> s'.suid <> s.suid) !to_do;
      let rec rml acc k = function
        | [] -> (false, List.rev acc)
        | (_,_,_,_,k' as c)::l -> if k = k' then (true, List.rev_append acc l)
                         else rml (c::acc) k l
      in
      let rec fn area acc l =
        if !debug then Printf.eprintf "%d+%d faces\n%!" (List.length l) (List.length acc);
        match l with
        | []       -> (acc,area)
        | (i,s,sg,b,key as c)::l ->
           if !debug then Printf.eprintf "test face %d (%b,%b) of %a\n%!"
                            i sg b print_simplex s.s;
           let l0 = try Hashtbl.find by_face key with Not_found -> [] in
           match l0 with
           | [(j,sg',s')] ->
              let test_sg = if sg=sg' then b else not b in
              if !debug then Printf.eprintf "next simplex tested with %b is %a\n%!"
                                test_sg print_simplex s'.s;
              if visible s' test_sg x then
                begin
                  if !debug then Printf.eprintf "to remove\n%!";
                  let acc = ref acc in
                  let l   = ref l   in
                  rm_s s';
                  if s'.k <> Unknown then total := Stdlib.(!total -. s'.f);
                  to_do := List.filter (fun s -> s'.suid <> s.suid) !to_do;
                  Array.iteri (fun k _ ->
                      if k <> j then
                        begin
                          let (key,sg'') = face_key s' k in
                          let (b,l')  = rml [] key !l   in
                          if not b then
                            begin
                              if !debug then Printf.eprintf "adding face %d (%b,%b) of %a\n%!"
                                               k sg'' test_sg print_simplex s'.s;
                              l := (k,s',sg'',test_sg,key) :: l'
                            end
                          else l := l';
                        end) s'.s;
                  fn Stdlib.(area+.s'.f) !acc !l
                end
              else
                fn area (c::acc) l
           | l -> Printf.printf "len: %d\n%!" (List.length l); assert false
      in
      let faces = List.init (Array.length s.s) (fun i ->
                      let (k,sg) = face_key s i in
                      (i,s,sg,true,k)) in
      let (hole,area) = fn s.f [] faces in
      let area = Stdlib.(area /. float (List.length hole)) in
      let added =
        List.map (fun (i,s,_,b,_) ->
            let s' = Array.mapi (fun j y -> if i = j then
                                              if b then x else ch_sg x else y) s.s in
            mk ~f:area s') hole
      in
      let add_local acc s =
        List.fold_left (fun acc (i,j) ->
            let (_,key) = edge_key s.s.(i) s.s.(j) in
            let l = try Hashtbl.find by_edge key with Not_found -> assert false in
            List.fold_left (fun acc (_,_,s) -> re_add acc s) acc l) acc dirs
      in
      add_to_do (List.fold_left add_local added added);
    in

    let do_triangle x =
      let in_triangle s =
        let m = to_matrix s.s in
        let c = pcoord x m in
        Array.for_all (fun x -> x *. c.(0) >= zero) c
      in
      try
        Hashtbl.iter (fun _ l ->
            List.iter (fun (_,_,s) ->
                if in_triangle s then
                  begin
                    let save = !debug in
                    debug := true;
                    let b = decision s in
                    debug := save;
                    Printf.printf "found %b\n%!" (b <> Unknown);
                    raise Exit
                  end) l) by_face
      with
        Exit -> ()
    in

    let rec test () =
      match !to_do with
      | []   -> true
      | s::ls ->
         let d = decision s in
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
              display 100.0 (0.,0.) l (fun s -> to_matrix s.s) None;
            end;
          if !debug then ignore (input_line stdin);
        end;
 *)
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

    (*check ();*)

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
    (!polyhedrons, List.map (fun s -> to_matrix s.s) all, do_triangle)

end
