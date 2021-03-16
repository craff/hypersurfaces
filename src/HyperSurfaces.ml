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
  open B
  open V
  open Simp
  module D = Display.Make(R)

  let all_dirs d =
    let res = ref [] in
    for i = 0 to d - 2 do
      for j = i+1 to d-1 do
        res := (i,j)::!res
      done
    done;
    !res

  let iter_voisins fn l =
    let rec gn acc l =
      match l with
      | [x;y] ->
         fn (List.rev_append acc [x-1;y+1]);
         fn (List.rev_append acc [x+1;y-1]);
      | x::l ->
         kn (x+1::acc) (-1) l;
         if x > 0 then kn (x-1::acc) (+1) l;
         gn (x::acc) l
      | _ -> assert false
    and kn acc d l =
      match l with
      | [x] ->
         fn (List.rev_append acc [x+d]);
      | x::l ->
         fn (List.rev_append acc (x+d::l));
         kn (x::acc) d l
      | _ -> assert false
    in
    gn [] l

  let enum_in_simplex eval m nb =
    let lm = ref [] in
    let dim = Array.length m in
    let app l =
      let (c1,_) =
        List.fold_left (fun (acc,j) i ->
            (comb one acc (of_int i) m.(j),j+1)) (zero_v dim,0) l
      in
      normalise c1
    in
    let rec kn k c l =
      if List.length l = dim - 1 then
        begin
          let l = (k - c) :: l in
          (*assert (in_simplex s c1);*)
          let c1 = app l in
          let v1 = eval c1 in
          let bad = ref 0 in
          let test l = let c = app l in
                       if eval c <. v1 then incr bad;
                       if !bad > 2 then raise Exit
          in
          try
            iter_voisins test l;
            lm := c1 :: !lm
          with Exit -> ()
        end
      else
        for i = 0 to k - c do
          kn k (c+i) (i::l)
        done
    in
    kn nb 0 [];
    !lm

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
    | Active
    | Removed

  type point_type =
    | Single
    | Multi
    | Any

  type decision =
    | Depend of vector * simplicies list
    | NonZero
    | NonDege


  and simplicies =
    { s : simplex
    ; m : matrix
    ; d : R.t
    ; n : v Lazy.t array
    ; p : polynomial list
    ; dp : polynomial_v lazy_t list
    ; l : R.t array list
    ; c : R.t array
    ; mutable f : float
    ; mutable k : status
    ; mutable codim : int
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

  let fst3 (x,_,_) = x

  let triangulation param p0 =
    let restore_objects =
      if !Args.prog then Display.hide_all_objects ()
      else (fun () -> ())
    in
    let time0 = Unix.gettimeofday () in
    let dims = List.map dim p0 in
    let deg = List.map degree p0 in
    let p0 = List.map Poly.normalise p0 in
    let dim = List.hd dims in
    if not (List.for_all ((=) dim) dims) then failwith "inhomogeneous equations";
    let sdim = dim - List.length p0 in
    let dirs = all_dirs dim in
    let dp0 = List.map2 (fun p d -> (p, gradient p, hessian p, d)) p0 deg in
    let dp0 = List.filter (fun (_,_,_,d) -> d > 1) dp0 in
    let solver_stat = init_solver_stats () in
    let allp =
      List.map (fun (p,dp,hp,d) ->
          let module F = struct
              let dim = dim
              let max_steps = 10000
              let max_proj = 5
              let fun_min = epsilon2
              let lambda_min = epsilon2
              let eval c = fst (eval_tgrad dp c)
              let grad c = fst3 (eval_thess hp c)
              let stat = solver_stat
            end
          in
          let module S = Solve(F) in
          (p, F.eval, S.solve)) dp0
    in
    let allp =
      match dp0 with
      | [] | [_] -> allp
      | _ ->
         let eval_tgrad c =
           List.fold_left (fun acc (_,dp,_,_) ->
               let (tg,p) = eval_tgrad dp c in
               acc +++ tg //. p) (zero_v dim) dp0
         in
         (*let eval c = norm2 (eval_tgrad c) in*)
         let eval_thess c =
           List.fold_left (fun acc (_,_,hp,_) ->
               let (th,tg,p) = eval_thess hp c in
               let m2 = Array.init dim (fun i -> Array.init dim (fun j -> tg.(i) *. tg.(j) /. (p *. p))) in
               let m1 = Array.map (fun x -> x //. p) th in
               acc ++++ m1 ---- m2) (Array.init dim (fun _ -> zero_v dim)) dp0
         in
         let module F = struct
             let dim = dim
              let max_steps = 10000
              let max_proj = 5
              let fun_min = epsilon2
              let lambda_min = epsilon2
              let eval c = eval_tgrad c
              let grad c = eval_thess c
              let stat = solver_stat
            end
          in
          let module S = Solve(F) in
          ([], F.eval, S.solve) :: allp
    in

    let penal_allp sc =
      List.map (fun (p,dp,hp,d) ->
          let module F = struct
              let dim = dim
              let max_steps = 10000
              let max_proj = max_steps
              let fun_min = epsilon2
              let lambda_min = epsilon2
              let eval c =
                let denom = sc *.* c -. one in
                fst (eval_tgrad dp c) //. denom
              let grad c =
                let denom = sc *.* c -. one in
                let (tg,_) = eval_tgrad dp c in
                Array.map (fun v -> v //. denom) (fst3 (eval_thess hp c)) ----
                  Array.init dim (fun i ->
                      Array.init dim (fun j -> tg.(i) *. sc.(j) /. (denom *. denom)))
              let stat = solver_stat
            end
          in
          let module S = Solve(F) in
          (F.eval, S.solve)) dp0
    in
    let all = Hashtbl.create 1001 in
    let add s = Hashtbl.replace all s.suid s in
    let rm s  = Hashtbl.remove all s.suid in
    let by_edge = Hashtbl.create 1001 in
    let by_vertex = Hashtbl.create 1001 in
    let by_face = Hashtbl.create 1001 in
    let to_do = Array.make dim [] in
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
    let nb_single = ref 0 in
    let nb_multi  = ref 0 in
    let nb_any    = ref 0 in

    let count_point = function
      | Single -> incr nb_single
      | Multi  -> incr nb_multi
      | Any    -> incr nb_any
    in

    let total_count = ref 0 in

    let rm_s s =
      decomp_log "remove %a" print_simplex s.s;
      assert (s.k <> Removed);
      s.k <- Removed; rm s; rm_v s; rm_e s; rm_f s;
      decr total_count;
    in
    let add_s s = add s; add_v s; add_e s; add_f s in

    let face_normal m i =
      let n =
        Array.init dim (fun j ->
            let b_j = Array.init dim (fun k -> if k = j then one else zero) in
            let m' = Array.mapi (fun j y -> if i = j then b_j else y) m in
            det m')
      in
      let n = if n *.* m.(i) >. zero then opp n else n in
      normalise n
    in

    let ls = quadrants dim in
    let s0 = to_matrix (List.hd ls) in

    let lm =
      List.fold_left (fun acc (p,evalc,solve) ->
          let evalc x = norm2 (evalc x) in
          let sdim = Stdlib.(truncate (sqrt (float dim))) in
          let lm =
            List.flatten (
                List.map
                  (fun s -> enum_in_simplex evalc (to_matrix s) (param.Args.crit / sdim)) ls)
          in
          List.fold_left (fun acc x ->
              try
                let (c1,fc1) = solve normalise (one /. of_int 1000) x in
                let pc = abs (eval p c1) in
                let ty = if pc =. zero then Multi else Single in
                (ty,pc,c1,fc1)::acc
              with Not_found -> acc) acc lm) [] allp
    in
    let lm = List.sort_uniq compare lm in
    let lm = ref (Array.of_list lm) in

    for i = 0 to (min dim (Array.length !lm)) - 1 do
      let eval (_,p,c,_) = if i = 0 then p else distance (Array.map (fun (_,_,c,_) -> c) !lm) i c in
      let best_i = ref i in
      let best   = ref (eval !lm.(i)) in
      for j = i + 1 to Array.length !lm - 1 do
        let v = eval !lm.(j) in
        (*printf "test %d %d: %a => %a, %a\n%!" i j print_vector (let (_,c,_)= !lm.(j) in c) print v print (let (_,_,x) = !lm.(j) in x);*)
        if v >. !best then (best:= v; best_i := j)
      done;
      let x = !lm.(i) in
      !lm.(i) <- !lm.(!best_i);
      !lm.(!best_i) <- x;
      (*printf "keep %d: %a => %a\n%!" i print_vector (let (_,c,_) = !lm.(i) in c) print !best ;*)
    done;

    let lm = if Array.length !lm < dim then !lm else Array.sub !lm 0 dim in
    let lm = ref (Array.map (fun (ty,_,c,_) -> count_point ty; c) lm) in
    while Array.length !lm < dim do
      let m = Array.init (Array.length !lm + 1) (fun i ->
                  if i = 0 then Array.init dim (fun i -> of_float (Random.float 1.0))
                  else !lm.(i-1))
      in
      let b = Array.init (Array.length !lm + 1) (fun i ->
                  if i = 0 then one else zero)
      in
      let c = m **- solve (m **** transpose m) b in
      let c = normalise c in
      count_point Any;
      lm := Array.append !lm [|c|]
    done;

    (*printf "init: %a\n%!" print_matrix lm;*)

    let lm = Array.map (fun c ->
      let (c,b) = if c.(dim-1) <. zero then (opp c,false) else (c,true) in
      Simp.mk c b) !lm
    in

    let rec gn acc q i =
      if i < 0  then q::acc
      else
        begin
          let q' = Array.copy q in
          q'.(i) <- ch_sg q'.(i);
          gn (gn acc q' (i-1)) q (i-1)
        end
    in
    let ls = gn [] lm (dim-2) in

    let n = List.length ls in

    let mk ?(f=Stdlib.(1.0 /. float_of_int n)) s =
      let m = to_matrix s in
      let n = Array.init dim (fun i -> lazy (face_normal m i)) in
      let p = List.map (fun p -> Poly.transform p s0 m) p0 in
      let l = List.map plane p in
      let c = center m in
      let dp = List.map (fun p -> lazy (gradient p)) p in
      let s = { s; m; p; k = Active; c; l; dp; f; n; d = det m
              ; codim = 0; suid = simplex_key s } in
      decomp_log "make %a" print_simplex s.s;
      add_s s;
      incr total_count;
      s
    in

    let total = ref 0.0 in

    to_do.(0) <- List.map (fun s -> mk s) ls;
    decomp_log "init simplicies done";
    let add_to_do dim l =
      if dim <> 0 then
        List.iter (fun s -> Stdlib.(total := !total +. float dim *. s.f);
                            s.codim <- dim) l;
      to_do.(dim) <- l @ to_do.(dim)
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

    let constant_sign2 (l, p) =
      let ap = ref true in
      let an = ref true in
      let nz = ref 0    in
      let fn (_,c) =
        let t = cmp c zero in
        if t < 0 then ap := false;
        if t > 0 then an := false;
        if t = 0 then incr nz;
      in
      List.iter fn p; List.iter fn l;
      (!an || !ap) && !nz <= sdim
    in

    let is_vertex m =
      Array.fold_left (fun n m -> if m > 0 then n+1 else n) 0 m = 1
    in

    let sub dps is =
      List.map (fun dp ->
          let res = ref [] in
          List.iter (fun (m,v) ->
              try
                for i = 0 to dim-1 do
                  if m.(i) <> 0 && not is.(i) then raise Exit;
                done;
                if is_vertex m || v <>. zero then
                  res := (m,v) :: !res
              with Exit -> ()) dp;
          !res) dps
    in

    let sub_v dps is =
      List.map (fun dp ->
          let res = ref [] in
          List.iter (fun (m,v) ->
              try
                for i = 0 to dim-1 do
                  if m.(i) <> 0 && not is.(i) then raise Exit;
                done;
                let n = norm2 v in
                if is_vertex m || n <>. zero then res := (m,v) :: !res
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
               let prev_sign = ref None in
               let eq v w =
                 if v.uid = w.uid then
                   match !prev_sign with
                   | None ->
                      prev_sign := Some (v.p = w.p); true
                   | Some s ->
                      s = (v.p = w.p)
                 else false
               in
               Array.iteri (fun i b ->
                   if b && Array.for_all (fun v -> not (eq v s.(i))) s'.s
                   then raise Not_found) vs;
               true
             with
               Not_found -> false
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
      let sd = List.map snd ls in
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
      (sd,!gd)
    in

    let visible_v s x =
      let sg, x = if x *.* s.c <. zero then (false, opp x) else (true, x) in
      let fn acc v =
        let d = x --- v in
        let d2 = norm2 d in
        match acc with
        | None -> Some(d,d2)
        | Some(_,d2') -> if d2 <. d2' then Some(d,d2) else acc
      in
      let d = match Array.fold_left fn None s.m with
        | None -> assert false
        | Some(d,_) -> d
      in
      (sg, d *.* s.c >. of_float param.Args.dprec *. epsilon)
    in

    let visible s x =
      let x = to_vec x in
      visible_v s x
    in

    (*
    let proj_simplex s x =
      let is_far = ref false in
      let m = ref [] in
      let y = ref [] in
      Array.iteri (fun i _ ->
          let n = Lazy.force s.n.(i) in
          let c = n *.* x in
          if c >. zero then
            begin
              is_far := true;
              m := n :: !m;
              y := c :: !y
            end
        ) s.m;
      if !is_far then
        begin
          let m = Array.of_list !m in
          let y = Array.of_list !y in
          let d = m **- solve (m **** transpose m) y in
          let r = normalise (x --- d) in
          (r, true)
        end
      else (normalise x, false)
    in
 *)
    let search_critical sd =
      let select x (s,dy,_,sy,fy as y) =
        assert (fy >=. zero);
        assert (dy >=. zero);
        match x with
        | None -> Some y
        | Some (_,dx,_,sx,fx) ->
           (match compare dx dy with
            | -1 -> x
            | _ -> Some y)
      in
      let best = ref None in
      let rec kn s =
        let c0 as center = normalise s.c in
        let radius2 = dist2 (to_vec s.s.(0)) c0 in
        let rs2 = radius2 /. of_int 100_000 in
        let fn best (p, evalc, solve) c0 =
          try
            let project c =
              let c = normalise c in
              let d = abs (c *.* s.c) in
              if d >. of_float 0.9999 then
                c
              else
                raise Exit
            in
            let (c1,fc1) = solve project rs2 c0 in
            assert(fc1 >=. zero);
            let (b1,b2) = visible_v s c1 in
            let c1 = if not b1 then opp c1 else c1 in
            if not b2 || fc1 >. (of_float 1e-28) then (Vector.sol_log "reject %b %b" b2 (fc1 >. epsilon); raise Not_found);
            let p2 = eval p c1 in
            select best (s, abs p2, c1, c1 *.* s.c, fc1)
          with Not_found -> best
        in
        List.iter (fun (_,evalc,_ as solve) ->
            let evalc x = norm2 (evalc x) in
            let lm = enum_in_simplex evalc s.m (param.Args.crit) in
            List.iter (fun c -> best := fn !best solve c) lm)  allp
      in
      List.iter kn sd;
      let (s, c, ty) = match !best with
        | None -> Vector.sol_log "keep nothing\n%!"; raise Not_found
        | Some (s, pc, c, sc, fc) ->
           Vector.sol_log "keep %a with sc: %a, fc: %a"
             print_vector c print sc print fc;
           let ty = if pc =. zero then Multi else Single in
           (s, c, ty)
      in
      let (c,b) = if c.(dim-1) <. zero then (opp c,false) else (c,true) in
      (s, Simp.mk c b, ty)
    in

    let open struct exception Zih of vector * simplicies list end in

    let decision_face vs (s as s0) =
      (* let vsf = Array.map (fun b -> if b then 1 else 0) vs in
         printf "decision for %a,%a\n%!"
         print_matrix (to_matrix s.s) print_int_array vsf;*)
      let p = sub s.p vs in
      let len = Array.length vs in
      let nb_vs = Array.fold_left (fun acc c -> if c then acc+1 else acc) 0 vs in
      let l = List.map first_deg p in
      let dp = sub_v (List.map Lazy.force s.dp) vs in
      let (sd,gd) = all_gradients vs s in

      let rec hn subd s l p dp =
        let lp = List.combine l p in
        let cst = List.exists constant_sign2 lp in
        (*printf "cst: %b, subd: %d\n%!" cst subd;*)
        if not cst then
          begin
            let rec fn points dps gds =
              match (dps, gds) with
              | [dp], [gd] ->
                 let dp = List.map snd dp in
                 let new_points = dp @ gd in
                 zih (new_points @ points)
              | dp::dps, gd::gds ->
                 let dp = List.map snd dp in
                 let new_points = dp @ gd in
                 let opp_new = List.map opp new_points in
                 fn (new_points @ points) dps gds ||
                   fn (opp_new @ points) dps gds
              | _ -> assert false
            in
            let res = fn [] dp gd in
            match res with
            | false -> (*printf "OK\n%!";*) ()
            | true when subd <= 0 || nb_vs = 1 ->
               let p = zero_v dim in
               Array.iteri (fun i x -> if vs.(i) then addq p x) s0.m;
               normaliseq p;
               (*printf "Zih\n%!";*) raise (Zih (p,sd))
            | true ->
               begin
                 let best = ref (-.one, (-1,-1)) in
                 for i = 1 to len - 1 do
                   if vs.(i) then
                     for j = 0 to i-1 do
                       if vs.(j) then
                         let c = norm2 (s.(i) --- s.(j)) in
                         if c >. fst !best then best := (c,(j,i))
                     done
                 done;
                 let (i,j) = snd !best in
                 assert (i >= 0 && j >= 0 && i <> j);
                 (*printf "split %d %d\n%!" i j;*)
                 let l1,l2 =
                   List.split (List.map (fun p -> subdivise p i j) l) in
                 let p1,p2 =
                   List.split (List.map (fun p -> subdivise p i j) p) in
                 let dp1,dp2 =
                   List.split (List.map (fun p -> subdivise_v p i j) dp) in
                 let s1 = Array.mapi (fun k x ->
                              if k = j then (x +++ s.(i)) //. of_int 2 else x) s in
                 let s2 = Array.mapi (fun k x ->
                              if k = i then (x +++ s.(j)) //. of_int 2 else x) s in
                 hn (subd-1) s1 l1 p1 dp1; hn (subd-1) s2 l2 p2 dp2
               end
          end
      in
      hn param.Args.subd s.m l p dp
    in

    let enum_facets codim dim =
      let r = ref [] in
      let vs = Array.make dim false in
      let rec fn codim i =
        if i >= dim then
          begin
            if Array.exists (fun b -> b) vs then
              r := Array.copy vs :: !r
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
      fn codim 0;
      !r
    in

    let decision codim s =
      try
        if List.exists constant_sign s.p then NonZero else
          let fn (_,vs) = decision_face vs s in
          let size vs =
            let best = ref inf in
            let m = Array.copy s.m in
            for i = 0 to dim - 1 do
              let v = m.(dim - 1) in
              m.(dim - 1) <- m.(i);
              m.(i) <- v;
              let s = distance m (dim - 1) m.(i) in
              if s <. !best then best := s
            done;
            !best
          in
          let facets = enum_facets (Some codim) dim in
          let facets = List.map (fun vs -> size vs, vs) facets in
          let facets = List.sort (fun (x,_) (y,_) -> compare y x) facets in
          List.iter fn facets; NonDege
      with
      | Zih (v,sd) -> Depend (v,sd)
      | e -> eprintf "got except: %s\n%!" (Printexc.to_string e);
                assert false
    in

    let ajoute s x ty =
      let (sg, v) = visible s x in
      assert ((v && sg) ||
        let x = to_vec x in
        let m = Array.map (fun p -> p --- x) s.m in
        let m' = Array.map (fun p -> p +++ x) s.m in
        printf "\nx(%b,%b): %a(%a)\nc: %a(%a)\ns:%a => %a\n%a => %a\n%a => %a\n%!" sg v
          print_vector x print (norm2 x)
          print_vector s.c print (x *.* s.c -. one)
          print_matrix s.m print_vector (Array.map (fun x -> x *.* s.c -. one) s.m)
          print_matrix m print (det m)
          print_matrix m' print (det m');
        false);
      assert (s.k = Active);
      total := Stdlib.(!total -. float s.codim *. s.f);
      count_point ty;
      rm_s s;
      decomp_log "adding center %a" print_vector (to_vec x);
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
              assert(s'.k <> Removed);
              if v' then
                begin
                  let i0 = if i = 0 then 1 else 0 in
                  let j0 = ref 0 in
                  while s'.s.(!j0).uid <> s.s.(i0).uid && !j0 < dim do incr j0 done;
                  let j0 = !j0 in
                  assert (j0 < dim);
                  assert (dim > 2);
                  decomp_log "to remove";
                  assert (s.s.(i0).uid = s'.s.(j0).uid);
                  let good = (sg = sg') = (s.s.(i0).p = s'.s.(j0).p) in
                  let acc = ref acc in
                  let l   = ref l   in
                  total := Stdlib.(!total -. float s'.codim *. s'.f);
                  rm_s s';
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
            let r = mk ~f:area s' in
            decomp_log "after mk";
            r
          ) hole
      in
      let ok = ref true in
      Hashtbl.iter (fun k l -> if List.length l <> 2 then
        (ok := false; eprintf "len = %d for key %a\n%!"
                        (List.length l) print_face_key k)) by_face;
      assert !ok;
      add_to_do 0 added;
    in

    let test codim =
      let order s1 s2 = Stdlib.compare (abs s2.d) (abs s1.d) in
      let ls = List.filter (fun s -> s.k <> Removed) to_do.(codim) in
      let ls = List.sort order ls in
      to_do.(codim) <- [];
      let gn s = decision (codim mod dim) s in
      let ds = List.map gn ls in
      List.iter2 (fun s d ->
        assert (s.codim >= codim);
        if (s.k <> Removed && s.codim = codim) then
          match d with
          | Depend(v,sd) ->
             assert (s.k = Active);
             if List.exists (fun s -> s.k = Removed) sd then
               begin
                 to_do.(codim) <- s :: to_do.(codim)
               end
             else
               begin
                 try
                   let (s,c,ty) = search_critical sd in
                   ajoute s c ty
                 with Not_found ->
                   let project c =
                     let c = normalise c in
                     let d = c *.* s.c in
                     if d >. of_float 1.01 then
                       c
                     else
                       raise Exit
                   in
                   let cs x = List.map (fun (eval,solve) ->
                                  let (c,_) = solve project (-.one) x in
                                  (c,norm2 (eval c))
                                ) (penal_allp s.c) in
                   let c = normalise s.c in
                   let cs = cs v @ cs c in
                   let best = ref (c, inf) in
                   List.iter (fun (c,fc) ->
                       if fc <. snd (!best) then best := (c, fc)) cs;
                   let (c,_) = !best in
                   let (c,b) = if c.(dim-1) <. zero then (opp c,false) else (c,true) in
                   ajoute s (Simp.mk c b) Any
               end
          | NonZero | NonDege ->
             total := Stdlib.(!total +. s.f);
             s.codim <- s.codim + 1;
             if s.codim < dim then to_do.(s.codim) <- s :: to_do.(s.codim)
        ) ls ds;
    in

    let print_total codim =
      let x = match to_do.(codim) with
        | [] -> 0.0
        | s::_ -> s.f
      in
      let time1 = Unix.gettimeofday () in
      let dt = Stdlib.(time1 -. time0) in
      let (hd,tail) = if Debug.has_debug () then "", "\n" else "\r", "" in
      eprintf "%s%7.3f%% %06d/%06d pts:%3d=%3d+%3d+%3d, codim: %d/%d, worst:%5.2e, time: %3.1fs%s%!"
        hd Stdlib.(!total *. 100.0 /. float dim)
        (List.length (List.filter (fun s -> s.k <> Removed) to_do.(codim)))
        !total_count
        (!nb_single + !nb_multi + !nb_any) !nb_single !nb_multi !nb_any
        codim (dim-1) x dt tail;
    in

    let erase_total () =
      let str = String.make 79 ' ' in
      eprintf "\r%s\r" str
    in

    let tmp_object = ref None in

    let display_current () =
      let edges = Hashtbl.fold (fun _ l acc ->
                      match l with
                      | [] -> assert false
                      | (i,j,s)::_ -> [|s.m.(i); s.m.(j)|]::acc)
                    by_edge []
      in
      (match !tmp_object with
       | None -> ()
       | Some o -> Display.rm_object o);
      let o = D.mk_lines_from_polyhedron "tmp_build" edges in
      o.visible <- true;
      tmp_object := Some o;
      if !Args.progw then Display.wait ();
    in

    while not (Array.for_all (fun l -> l = []) to_do) do
      let codim =
        let res = ref 0 in
        try
          for i = 0 to dim-1 do
            res := i; if to_do.(i) <> [] then raise Exit
          done;
          assert false;
        with
          Exit -> !res
      in
      print_total codim;
      if !Args.prog then display_current ();
      test codim;
    done;

    if !Args.prog then display_current ();
    eprintf "\r                                                         \r%!";

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
        List.iter gn (enum_facets None dim)
      in
      List.iter fn faces;
      !res
    in

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
          List.iter (fun (i,j) -> add_edge edges i j s) dirs;
          true
        end
      else
        false
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
              assert (add_simplex dirs edges simplices s1 l1);
              assert (add_simplex dirs edges simplices s2 l2)
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
        (* printf "s: %a, nb_keep: %d %d\n%!" print_simplex s nb_keep dim;*)
        assert (nb_keep <= dim);
        if nb_keep = dim then
          begin
            let s = Array.of_list (List.map (fun i -> s.(i)) keep) in
            let l = List.map (fun v ->
                        Array.of_list (List.map (fun i -> v.(i)) keep)) l in
            let _ = add_simplex new_dirs new_edges new_simplices s l in
            (*if is_new then
              begin
                printf "keep: %a, " print_simplex s;
                List.iter (fun v -> printf "%a " print_vector v) l;
                print_newline();
              end*)
            ()
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
    erase_total ();
    printf "total: %d/%d pts:%d=%d+%d+%d, time: %fs, %t, %a\n" keep total
      (!nb_single + !nb_multi + !nb_any) !nb_single !nb_multi !nb_any
      dt print_zih_stats print_solver_stats solver_stat;
    let cps = components all in
    let chr = List.map euler cps in
    printf "%d components %a\n%!" (List.length cps) print_int_list chr;
    begin
      let open Args in
      match param.expected with
      | Anything -> ()
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
                    | (i,j,s)::_ -> [|s.m.(i); s.m.(j)|]::acc)
                  by_edge []
    in

    restore_objects ();
    (List.map to_matrix all, edges)

end
