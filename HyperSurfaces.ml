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
    { s : matrix
    ; p : polynomial
    ; l : R.t array
    ; f : float
    ; mutable x : float
    ; mutable d : int * int
    ; mutable k : bool }

  let order s1 s2 =
    match compare s2.x s1.x with
    | 0 -> compare s2.f s1.f
    | c -> c

  let vertex_key deg v1 =
    let v2 = Array.map (~-.) v1 in
    let v = max v1 v2 in
    (v == v1, v)

  let edge_key s i j =
    let v1 = s.s.(i) and v2 = s.s.(j) in
    let v1' = Array.map (~-.) v1 in
    let v2' = Array.map (~-.) v2 in
    let m = max (max v1 v2) (max v1' v2') in
    if m == v1 then (v1,v2)
    else if m == v2 then (v2,v1)
    else if m == v1' then (v1',v2')
    else (v2',v1')

  let eval dirs dim deg ({s;p;l=l0} as s0) =
    if !debug then Printf.eprintf "eval %a => %a\n%!" print_matrix s print_vector l0;
    let best = ref zero in
    let best_i = ref 0 in
    let best_j = ref 0 in
    let dp = tgradient p in
    let t = Array.init dim (fun i -> List.assoc (var_power i dim (deg-1)) dp) in
    try
      List.iter (fun (i,j) ->
          let x = dist2 s.(i) s.(j) in
          let y = t.(i) *.* t.(j) in
          let zi = Array.for_all (fun x -> cmp x zero = 0) t.(i) in
          let zj = Array.for_all (fun x -> cmp x zero = 0) t.(j) in
          if zi && zj then (best_i := i; best_j := j; raise Exit);
          if not zi && not zj then
            begin
              let z = x /. (y *. y /. (t.(i) *.* t.(i)) /. (t.(j) *.* t.(j)) +. one) in
              if cmp z !best > 0 then (best := x; best_i := i; best_j := j)
            end) dirs;
      if !debug then Printf.eprintf "eval => %a (%d, %d)\n%!" print !best !best_i !best_j;
      s0.x <- to_float !best;
      s0.d <- (!best_i,!best_j)
    with Exit ->
      s0.x <- max_float;
      s0.d <- (!best_i,!best_j)


  let decision tbl deg dim {s; d; p; l=l0} =
    let gd =
      let gd = ref (tgradient p) in
      Array.iteri (fun i v ->
          let (b1,key) = vertex_key deg v in
          let ls = try Hashtbl.find tbl key with Not_found -> assert false in
          List.iter (fun (b2,({l} as s')) ->
              assert (b1 = b2 || v.(dim-1) = zero);
              let l0 = if deg mod 2 <> 0 && b1 <> b2 then Array.map (~-.) l else l in
              let s2 = if b1 = b2 then s'.s else
                         Array.map (Array.map (~-.)) s'.s
              in
              let l = transform l0 s2 s in
              if !debug then Printf.eprintf " %d %a at %a => %a => %a\n%!"
                               i print_matrix s'.s print_vector v
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
    if !debug then Printf.eprintf "test for %d points for\n %a\n%!" (Array.length gd)
      print_matrix s;
    if !debug then Array.iter (fun (l,v) -> Printf.eprintf " %a %a\n%!"
                                              print_list l print_vector v) gd;
    zero_in_hull gd

  let filter_map f l =
    let rec fn = function
      | [] -> []
      | x::l ->
         try
           f x :: fn l
         with Not_found ->
           fn l
    in
    fn l

  let _ = Printexc.record_backtrace true

  let triangulation p0 =
    let dim = dim p0 in
    let deg = degree p0 in
    let dirs = all_dirs dim in
    let open Stdlib in
    let p0 = complete p0 in
    let qs = quadrants p0 in
    let n = List.length qs in
    let by_vertex = Hashtbl.create 1001 in
    let add_v s =
      Array.iter (fun v ->
          let (b,key) = vertex_key deg v in
          let l = try Hashtbl.find by_vertex key with Not_found -> [] in
          Hashtbl.replace by_vertex key ((b,s)::l)) s.s
    in
    let rm_v s =
      Array.iter (fun v ->
          let (_,key) = vertex_key deg v in
          let l = try Hashtbl.find by_vertex key with Not_found -> assert false in
          let l = List.filter (fun (_,s') -> s != s') l in
          Hashtbl.replace by_vertex key l) s.s
    in

    let mk ?(f=1.0 /. float_of_int n) ?(k=false) s p =
      let s =
        { s; p; x=0.0; d=(0,0); k
        ; l = plane p
        ; f }
      in
      add_v s;
      eval dirs dim deg s;
      s
    in
    let qs = List.map (fun (s,p) -> mk s p) qs in
    let qs = ref (List.sort order qs) in
    let total = ref 0.0 in
    let nb_keep = ref 0 in
    let nb_remove = ref 0 in
    let splitted = Hashtbl.create 1001 in

    let rec test acc l =
      match l with
      | []   -> true
      | s::l ->
         if not s.k && decision by_vertex deg dim s
         then
           begin
             let (i,j) = s.d in
             let (p1,p2) = subdivise2 s.p i j in
             let (s1,s2) = split s.s i j in
             if !debug then
               begin
                 Printf.eprintf "quadrant: %a\n%!" print_matrix s.s;
                 Printf.eprintf "polynome: %a\n%!" print_polynome s.p;
                 Printf.eprintf "split (%d,%d) for %f\n%!" i j s.x;
                 Printf.eprintf "quadrant(1): %a\n%!" print_matrix s1;
                 Printf.eprintf "polynome (1): %a\n%!" print_polynome p1;
                 Printf.eprintf "quadrant(2): %a\n%!" print_matrix s2;
                 Printf.eprintf "polynome (2): %a\n%!" print_polynome p2;
               end;
             rm_v s;
             let f = s.f /. 2.0 in
             let s1 = mk ~f s1 p1 in
             let s2 = mk ~f s2 p2 in
             let key = edge_key s i j in
             Hashtbl.add splitted key ();
             qs := List.rev_append acc (s1::s2::l);
             false
           end
         else
           begin
             if not s.k then (s.k <- true; total := !total +. s.f);
             test (s::acc) l
           end
    in
    let rec fsplit acc l =
      match l with
      | []   -> qs := List.rev acc
      | s::l ->
         try
           let (i,j) = List.find (fun (i,j) ->
             let key = edge_key s i j in
             Hashtbl.mem splitted key) dirs
           in
           let (p1,p2) = subdivise2 s.p i j in
           let (s1,s2) = split s.s i j in
           if !debug then
             begin
               Printf.eprintf "quadrant: %a\n%!" print_matrix s.s;
               Printf.eprintf "polynome: %a\n%!" print_polynome s.p;
               Printf.eprintf "early split (%d,%d)\n%!" i j;
               Printf.eprintf "quadrant(1): %a\n%!" print_matrix s1;
               Printf.eprintf "polynome (1): %a\n%!" print_polynome p1;
               Printf.eprintf "quadrant(2): %a\n%!" print_matrix s2;
               Printf.eprintf "polynome (2): %a\n%!" print_polynome p2;
             end;
           rm_v s;
           let f = s.f /. 2.0 in
           let s1 = mk ~f ~k:s.k s1 p1 in
           let s2 = mk ~f ~k:s.k s2 p2 in
           fsplit (s1::s2::acc) l
         with
           Not_found -> fsplit (s::acc) l
    in

    while not (test [] !qs) do
      fsplit [] !qs;
      qs := List.sort order !qs;
      let x = match !qs with
        | [] -> assert false
        | s::_ -> s.x
      in
      if dim = 3 then
        begin
          let open Graphics in
          clear_graph ();
          display 100.0 (0.,0.) !qs (fun s -> s.s);
          if !debug then ignore (input_line stdin);
        end;
      if !debug then
        begin
          Printf.eprintf "%f%% %f\n%!" (!total *. 100.0) x;
          ignore (input_char stdin);
        end
      else
        Printf.eprintf "\r%f %f%%                        %!" (!total *. 100.0) x;
    done;

    let polyhedrons = ref [] in
    List.iter (fun {s;p} ->
        let plane = List.combine (Array.to_list s) (Array.to_list (plane p)) in
        let pos,neg = List.partition (fun (p,x) -> cmp x zero > 0) plane in
        if !debug then
          begin
            Printf.eprintf "quadrant: %a\n%!" print_matrix s;
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
                           digho p0 (one /. of_int 1000) x p y q
                           (*let t = y /. (y -. x) in
                           let u = x /. (x -. y) in
                           comb t p u q*) :: acc) acc neg) [] pos
          in
          let ph = Array.of_list ph in
          if !debug then
            Printf.eprintf "keep polyedron: %a\n%!" print_matrix ph;
          polyhedrons := ph :: !polyhedrons;
          incr nb_keep) !qs;
    Printf.eprintf "total: %d, kept: %d, removed %d\n%!"
                   (!nb_keep + !nb_remove) !nb_keep !nb_remove;
    List.iter (fun ph ->
        Printf.eprintf "  %a\n%!" print_matrix ph) !polyhedrons;
    !polyhedrons, (List.map (fun s -> s.s) !qs)

end
