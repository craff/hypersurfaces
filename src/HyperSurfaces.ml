open Printing

let decomp_log = Debug.new_debug "decomposition" 'd'
let decomp_tst = decomp_log.tst
let decomp_log fmt = decomp_log.log fmt

let solver1_chrono = Chrono.create "solver1"
let solver2_chrono = Chrono.create "solver2"
let solver3_chrono = Chrono.create "solver3"
let test_chrono = Chrono.create "test"
let add_chrono = Chrono.create "add"

let chr_solve1 s a b c = Chrono.add_time solver1_chrono (s a b) c
let chr_solve2 s a b c = Chrono.add_time solver2_chrono (s a b) c
let chr_solve3 s a b c = Chrono.add_time solver3_chrono (s a b) c

module Make(R:Field.SPlus) = struct
  open R
  module Simp = Simplices.Make(R)
  module Poly = B
  open B
  open V
  open Simp
  module D = Display.Make(R)

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

  type point_type =
    | Single
    | Multi
    | Any
    | Center


  let print_ty ch = function
    | Single -> fprintf ch "S"
    | Multi -> fprintf ch "M"
    | Any -> fprintf ch "A"
    | Center -> fprintf ch "C"

  type decision =
    | Depend of vector * vector list * (bool * simplicies) list
    | NonZero
    | NonDege

  and simplicies = data simplex

  and data =
    { p : polynomial list
    ; dp : polynomial_v lazy_t list
    ; l : R.t array list
    ; mutable f : float
    ; mutable codim : int
    }

  let h = one /. of_int 2

  let fst3 (x,_,_) = x

  let triangulation param p0 =

    let restore_objects =
      if !Args.prog then Display.hide_all_objects ()
      else (fun () -> ())
    in
    let dims = List.map dim p0 in
    let deg = List.map degree p0 in
    let p0 = List.map Poly.normalise p0 in
    let dim = List.hd dims in
    if not (List.for_all ((=) dim) dims) then failwith "inhomogeneous equations";
    let codim = List.length p0 in
    let sdim = dim - codim in
    let dirs = all_dirs dim in
    let dp0 = List.map2 (fun p d -> (p, gradient p, hessian p, d)) p0 deg in
    let dp0 = List.filter (fun (_,_,_,d) -> d > 1) dp0 in
    let solver1_stat = init_solver_stats () in
    let solver2_stat = init_solver_stats () in
    let solver3_stat = init_solver_stats () in
    let eval_prod c = (*
      let gs = List.map (fun (_,dp,_,_) -> eval_grad dp c) dp0 in
      let gs = Array.of_list gs in
      let m = gs **** transpose gs in
      det m*)
      List.fold_left (fun acc (p,_,_,_) ->
          let n = eval p c in
          acc +. n *. n) zero dp0
    in
    let single_critical =
      List.map (fun (_,dp,hp,_) ->
         let module F = struct
             let dim = dim
             let fun_min = epsilon2
             let fun_good = of_float param.Args.crit_limit
             let min_prog_coef = sqrt (of_int 2)
             let min_prog_int = 2 * dim
             let lambda_min = epsilon2
             let eval c = fst (eval_tgrad dp c)
             let grad c = fst3 (eval_thess hp c)
             let stat = solver1_stat
           end
         in
         let module S = Solve(F) in
         (Single, chr_solve1 S.solve)
        ) dp0
    in
    let multi_critical =
      match dp0 with
      | []|[_] -> []
      | _ ->
         List.init codim (fun i ->
             let dim0 = dim in
             let module F = struct
               let dim = dim + codim
               let fun_min = epsilon2
               let fun_good = of_float param.Args.crit_limit
               let min_prog_coef = sqrt (of_int 2)
               let min_prog_int = 2 * dim
               let lambda_min = epsilon2
               let eval c =
                 let x = Array.sub c 0 dim0 in
                 let l = Array.sub c dim0 codim in
                 let tg = zero_v dim0 in
                 let ps = zero_v (codim - 1) in
                 let s = ref (-. one) in
                 List.iteri
                   (fun j (_,dp,_,d) ->
                     let (tg',dp) = eval_tgrad dp x in
                     let p = dp /. of_int d in
                     s := !s +. l.(j) *. l.(j);
                     if j < i then ps.(j) <- p;
                     if j > i then ps.(j-1) <- p;
                     combq one tg l.(j) tg') dp0;
                 Array.init dim (fun j ->
                     if j < dim0 then tg.(j)
                     else if j - dim0 < codim - 1 then ps.(j-dim0)
                     else !s)
               let grad c =
                 let x = Array.sub c 0 dim0 in
                 let l = Array.sub c dim0 codim in
                 let ths = Array.init codim (fun j ->
                               let (_,_,hp,_) = List.nth dp0 j in
                               eval_thess hp x)
                 in
                 Array.init dim (fun j ->
                     let j' = j - dim0 in
                     Array.init dim (fun k ->
                         let k' = k - dim0 in
                         if j < dim0 then
                           if k < dim0 then
                             begin
                               let r = ref zero in
                               for m = 0 to codim - 1 do
                                 let (th,_,_) = ths.(m) in
                                 r := !r +. l.(m) *. th.(j).(k)
                               done;
                               !r
                             end
                           else
                             begin
                               let (_,tg,_) = ths.(k') in
                               tg.(j)
                             end
                         else if j' < codim - 1 then
                           if k < dim0 then
                             begin
                               let j' = if j' < i then j' else j' + 1 in
                               let (_,tg,_) = ths.(j') in
                               tg.(k)
                             end
                           else zero
                         else
                           if k < dim0 then zero else of_int 2 *. l.(k')))
               let stat = solver2_stat
           end
         in
         let module S = Solve(F) in
         let solve proj a x =
           let proj' x =
             let x' = proj (Array.sub x 0 dim) in
             let l' = normalise (Array.sub x dim codim) in
             Array.append x' l'
           in
           let z = sqrt (one /. of_int codim) in
           let x = Array.init F.dim (fun i ->
                       if i < dim then x.(i) else z)
           in
           let (fc,r) = S.solve proj' a x in
           (fc,Array.sub r 0 dim)
         in
         (Multi, chr_solve2 solve))
    in

    let penal_critical c0 =
      let nc0 = norm c0 in
      let penal x =
        let xc = x *.* c0 in
        let denom = xc -. one in
        if denom <=. zero then inf else
          let r = (nc0 -. one) /. denom in
          r *. r
      in
      List.map (fun (_,dp,hp,_) ->
          let module F = struct
              let dim = dim
              let fun_min = epsilon2
              let fun_good = inf
              let min_prog_coef = sqrt (of_int 2)
              let min_prog_int = 2 * dim
              let lambda_min = epsilon2
              let eval c =
                let p = penal c in
                let n = fst (eval_tgrad dp c) in
                p **. n
              let grad c = fst3 (eval_thess hp c)
              let stat = solver3_stat
            end
          in
          let module S = Solve(F) in
          (Any, chr_solve3 S.solve)) dp0
    in

    let nb_single = ref 0 in
    let nb_multi  = ref 0 in
    let nb_any    = ref 0 in
    let nb_center    = ref 0 in

    let count_point = function
      | Single -> incr nb_single
      | Multi  -> incr nb_multi
      | Any    -> incr nb_any
      | Center -> incr nb_center
    in

    let to_do = Array.make dim [] in

    let ls = quadrants dim in
    let s0 = List.hd ls in

    let lm =
      List.fold_left (fun acc (ty,solve) ->
          let lm =
            List.flatten (
                List.map
                  (fun s -> pts_in_simplex s param.Args.crit) ls)
          in
          List.fold_left (fun acc x ->
              try
                let proj = normalise in
                let (fc1,c1) = solve proj (one /. of_int 1000) x in
                (*                printf "fc1: %a %a\n%!" print fc1 print_ty ty;*)
                let pc = eval_prod c1 in
                if fc1 <. of_float param.Args.crit_limit then
                  (ty,pc,c1,fc1)::acc
                else
                  acc
              with Not_found -> acc
                  | _ -> assert false) acc lm) [] single_critical
    in

    let mk_sgn (ty,x,v,y) =
      let m = ref v.(0) in
      for i = 1 to Array.length v - 1 do
        if abs v.(i) >. abs !m then m := v.(i)
      done;
      let v = if !m <. zero then opp v else v in
      (ty,x,v,y)
    in
    let lm = List.map mk_sgn lm in
    let lm = List.sort_uniq compare lm in
    let lm = ref (Array.of_list lm) in

    for i = 0 to (min dim (Array.length !lm)) - 1 do
      let eval (_,p,c,_) =
        if i = 0 then p else
          min (distance (Array.map (fun (_,_,c,_) -> c) !lm) i c)
            (distance (Array.map (fun (_,_,c,_) -> c) !lm) i (opp c))
      in
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
                  if i = 0 then Array.init dim
                                  (fun _ -> of_float (Random.float 1.0))
                  else !lm.(i-1))
      in
      let b = Array.init (Array.length !lm + 1) (fun i ->
                  if i = 0 then one else zero)
      in
      try
        let c = m **- solve (m **** transpose m) b in
        let c = normalise c in
        count_point Any;
        lm := Array.append !lm [|c|]
      with Not_found -> ()
    done;

    decomp_log "init simplex: %a" print_matrix !lm;

    let lm = Array.map (fun c ->
      let (c,b) = if c.(dim-1) <. zero then (opp c,false) else (c,true) in
      Simp.mkv c b) !lm
    in

    let order s1 s2 = Stdlib.compare (abs s2.d) (abs s1.d) in

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
    let trs = empty_triangulation dim in

    let mk ?(f=Stdlib.(1.0 /. float_of_int n)) s =
      let m = Array.map to_vec s in
      let p = List.map (fun p -> Poly.transform p s0 m) p0 in
      let l = List.map plane p in
      let dp = List.map (fun p -> lazy (gradient p)) p in
      let o = { p; l; dp; f; codim = 0 } in
      let s = mks ~t:trs o s in
      decomp_log "make %a" print_simplex s;
      s
    in

    let total = ref 0.0 in

    to_do.(0) <- List.map mk ls;
    decomp_log "init simplicies done";
    let add_to_do l =
      to_do.(0) <- l @ to_do.(0)
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
      let nz = ref 0 in
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

    let all_gradients vs {s; m; o = {l=l0}; } =
      let l = ref [] in
      Array.iteri (fun i x -> if x then l := i :: !l) vs;
      let l = !l in
      let ls = match l with
        | []  -> assert false
        | [i] ->
           let l = try Hashtbl.find trs.by_vertex s.(i).uid
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
             try Hashtbl.find trs.by_edge k with Not_found -> assert false in
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
      List.iter (fun (opp,({o={l}} as s0')) ->
         let l0 =
           List.map2 (fun deg l ->
               if deg mod 2 <> 0 && opp then Array.map (~-.) l else l) deg l
         in
         let s2 =
           if opp then Array.init dim (fun i -> cev s0' i)
           else Array.init dim (fun i -> vec s0' i)
         in
         let l = List.map (fun l -> V.transform l s2 m) l0 in
         gd := List.map2 (fun l gd -> l :: gd) l !gd ;
        ) ls;
      (ls,!gd)
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

    let search_points critical allp sd =
      Thread.yield ();
      let select x (_,dy,_,sy,_,_ as y) =
        assert (dy >=. zero);
        match x with
        | None -> Some y
        | Some (_,dx,_,sx,_,_) ->
           match compare (dy*.sx) (dx*.sy) with
           | 1 -> x
           | _ -> Some y
      in
      let best = ref None in
      let kn (_,s) =
        let c0 = normalise s.c in
        let rs2 =
          if critical then
            let radius2 = dist2 (to_vec s.s.(0)) c0 in
            radius2 *. of_float 1e-12 /. of_int (param.crit * param.crit)
          else -. one
        in
        let fn best (ty,solve) c0 =
          try
            (*if not critical then printf "solve %a %a ==> " print_vector s.c print_vector c0;*)
            let proj =
              if critical then (*project_circle s.c 0.95*)
                fun c ->
                  let c = normalise c in
                  let d = c *.* s.c in
                  if d <. of_float 0.9 then raise Not_found;
                  c
              else
                let cen =
                  (((norm s.c -. one) *. of_float 0.9 +. one) /. norm s.c) **. s.c
                in
                project_circle cen 0.05
            in
            let (fc1,c1) = solve proj rs2 c0 in
            assert(fc1 >=. zero);
            let (b1,b2) = visible_v s c1 in
            (*if not critical then printf "fc1: %a %a %b %b\n%!" print fc1 print_ty ty b1 b2;*)
            if not b1 || not b2 || (critical && fc1 >=. of_float param.Args.crit_limit) then
              (
                assert critical;
                Vector.sol_log "reject %b %b %b" b1 b2 (fc1 >. epsilon); raise Not_found);
            let p2 = eval_prod c1 in
            select best (s, p2, c1, c1 *.* s.c, fc1, ty)
          with Not_found -> (*printf "NF\n%!";*) best
        in
        List.iter (fun solve ->
            let lm =
              if critical then pts_in_simplex s.m (param.Args.crit)
              else [s.c]
            in
            List.iter (fun c -> best := fn !best solve c) lm) allp
      in
      Vector.sol_log "begin iter";
      List.iter kn sd;
      Vector.sol_log "end iter";
      let (s, c, ty) = match !best with
        | None -> Vector.sol_log "keep nothing"; raise Not_found
        | Some (s, _, c, sc, fc, ty) ->
           Vector.sol_log "keep %a with sc: %a, fc: %a"
             print_vector c print sc print fc;
(*           if not critical then printf "keep %a with sc: %a, fc: %a\n%!"
             print_vector c print sc print fc;*)
           (s, c, ty)
      in
      let (c,b) = if c.(dim-1) <. zero then (opp c,false) else (c,true) in
      (s, Simp.mkv c b, ty)
    in

    let search_single_critical sd =
      search_points true single_critical sd
    in
    let search_multi_critical sd =
      search_points true multi_critical sd
    in
    let search_penal_critical c sd =
      search_points false (penal_critical c) sd
    in

    let open struct exception Zih of vector * vector list * (bool * simplicies) list end in

    let decision_face vs (s as s0) =
(*      let vsf = Array.map (fun b -> if b then 1 else 0) vs in
        printf "decision for %a,%a\n%!"
        print_matrix s.m print_int_array vsf;*)
      let p = sub s.o.p vs in
      let len = Array.length vs in
      let nb_vs = Array.fold_left (fun acc c -> if c then acc+1 else acc) 0 vs in
      let l = List.map first_deg p in
      let dp = sub_v (List.map Lazy.force s.o.dp) vs in
      let (sd,gd) = all_gradients vs s in

      let rec hn subd s l p dp =
        (*        printf "l:%a p:%a\n%!" (print_polynome ?vars:None) (List.hd l) (print_polynome ?vars:None) (List.hd p);*)
        let lp = List.combine l p in
        let cst = List.exists constant_sign2 lp in
        (*        printf "cst: %b, subd: %d %a\n%!" cst subd print_matrix s;*)
        if not cst then
          begin
            let rec fn points dps gds =
              match (dps, gds) with
              | [dp], [gd] ->
                 let dp = List.map snd dp in
                 let new_points = dp @ gd in
                 let all = new_points @ points in
                 if zih all then Some all else None
              | dp::dps, gd::gds ->
                 let dp = List.map snd dp in
                 let new_points = dp @ gd in
                 let opp_new = List.map opp new_points in
                 (match fn (new_points @ points) dps gds with
                  | None -> fn (opp_new @ points) dps gds
                  | r    -> r)
              | _ -> assert false
            in
            let res = fn [] dp gd in
            match res with
            | None -> (*printf "OK\n%!";*) ()
            | Some all when subd <= 0 || nb_vs = 1 ->
               begin
                 try
                   let l = ref [] in
                   Array.iteri (fun i x -> if vs.(i) then l:= x :: !l) s0.m;
                   let p = normalise (lcenter (Array.of_list !l)) in
                   (*printf "Zih\n%!";*) raise (Zih (p,all,sd))
                 with Not_found -> assert false
               end
            | Some _ ->
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
                 (*                 printf "split %d %d\n%!" i j;*)
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

    let count_common s s' =
      let r = ref 0 in
      for i = 0 to dim - 1 do
        let u = s.s.(i).uid in
        if Array.exists (fun x -> x.uid = u) s'.s then incr r
      done;
      !r
    in

    let re_add_neighbour s =
      for i = 0 to dim - 1 do
        let key = s.s.(i).uid in
        let l = try Hashtbl.find trs.by_vertex key with Not_found -> [] in
        List.iter (fun (_,s') ->
            let n = count_common s s' in
            assert (n > 0);
            let codim = dim - n in
            let old = s'.o.codim in
            if codim < old then
              begin
                to_do.(old) <- List.filter (fun s -> s != s') to_do.(old);
                s'.o.codim <- codim;
                to_do.(codim) <- s' :: to_do.(codim);
                total := Stdlib.(!total -. float (old - codim) *. s'.o.f);
              end) l
      done;
    in

    let decision codim s =
      Thread.yield ();
      try
        if List.exists constant_sign s.o.p then NonZero else
          let fn (_,vs) = decision_face vs s in
          let size vs =
            let m = Array.to_list s.m in
            let m = List.mapi (fun i x -> (vs.(i), x)) m in
            let m = List.filter fst m in
            let m = Array.of_list (List.map snd m) in
            det (m **** transpose m)
          in
          let facets = enum_facets (Some codim) dim in
          let facets = List.map (fun vs -> size vs, vs) facets in
          let facets = List.sort (fun (x,_) (y,_) -> compare y x) facets in
          List.iter fn facets; NonDege
      with
      | Zih (v,all,sd) -> Depend (v,all,(true,s)::sd)
      | e -> eprintf "got except: %s\n%!" (Printexc.to_string e);
                assert false
    in

    let ajoute s x = Chrono.add_time add_chrono (fun ty ->
      let (sg, v) = visible s x in
      assert ((v && sg) ||
        let x = to_vec x in
        let m = Array.map (fun p -> p --- x) s.m in
        let m' = Array.map (fun p -> p +++ x) s.m in
        printf "\nx(%b,%b,%a): %a(%a)\nc: %a(%a)\ns:%a => %a\n%a => %a\n%a => %a\n%!"
          sg v print_ty ty
          print_vector x print (norm2 x)
          print_vector s.c print (x *.* s.c -. one)
          print_matrix s.m print_vector (Array.map (fun x -> x *.* s.c -. one) s.m)
          print_matrix m print (det m)
          print_matrix m' print (det m');
        false);
      assert (s.k = Active);
      total := Stdlib.(!total -. float s.o.codim *. s.o.f);
      count_point ty;
      rm trs s;
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
             i print_simplex s print_face_key key;
           assert (s.k = Removed);
           let l0 = try Hashtbl.find trs.by_face key with Not_found -> [] in
           let (sg,v)   = visible s  x in
           assert v;
           match l0 with
           | [(j,s')] ->
              decomp_log "next simplex tested is %a" print_simplex s';
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
                  total := Stdlib.(!total -. float s'.o.codim *. s'.o.f);
                  rm trs s';
                  Array.iteri (fun k _ ->
                      if k <> j then
                        begin
                          let key' = face_key s'.s k in
                          let (b,l')  = rml [] key' !l   in
                          let (b',_)  = rml [] key' !acc   in
                          assert (b' = None);
                          match b with
                          | None ->
                             decomp_log "adding face %d of %a" k print_simplex s';
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
                  fn Stdlib.(area+.s'.o.f) !acc !l
                end
              else
                fn area (c::acc) l
           | _ ->
              decomp_log "len: %d for %a\n%!" (List.length l0) print_face_key key;
              assert false
      in
      let (hole,area) = if dim > 2 then fn s.o.f [] faces else (faces, s.o.f) in
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
                        (List.length l) print_face_key k)) trs.by_face;
      assert !ok;

      add_to_do added;
      List.iter re_add_neighbour added)
    in

    let test codim =
      let ls = List.filter (fun s -> s.k <> Removed) to_do.(codim) in
      let ls = List.sort order ls in
      to_do.(codim) <- [];
      let gn s = Chrono.add_time test_chrono (decision (codim mod dim)) s in
      let ds = List.map gn ls in
      eprintf "...";
      List.iter2 (fun s d ->
        if (s.k <> Removed && s.o.codim = codim) then
          match d with
          | Depend(v,_,sd) ->
             assert (s.k = Active);
             if List.exists (fun (_,s) -> s.k = Removed) sd then
               begin
                 to_do.(codim) <- s :: to_do.(codim)
               end
             else
               begin
                 try
                   let (s,c,ty) = search_single_critical sd in
                   ajoute s c ty
                 with Not_found -> try
                   let (s,c,ty) = search_multi_critical sd in
                   ajoute s c ty
                 with Not_found -> try
                   let (s,c,ty) = search_penal_critical s.c sd in
                   ajoute s c ty
                 with Not_found ->
                   let c = normalise v in
                   let (c,b) = if c.(dim-1) <. zero then (opp c,false) else (c,true) in
                   let c = Simp.mkv c b in
                   ajoute s c Center
               end
          | NonZero | NonDege ->
             total := Stdlib.(!total +. s.o.f);
             s.o.codim <- s.o.codim + 1;
             if s.o.codim < dim then to_do.(s.o.codim) <- s :: to_do.(s.o.codim)
        ) ls ds
    in

    let print_total codim =
      let x = match to_do.(codim) with
        | [] -> 0.0
        | s::_ -> s.o.f
      in
      let (hd,tail) = if Debug.has_debug () then "", "\n" else "\r", "" in
      eprintf "%s%6.3f%% %06d/%06d pts:%2d=%2d+%2d+%2d+%2d, codim: %d/%d, worst:%5.2e%s%!"
        hd Stdlib.(!total *. 100.0 /. float dim)
        (List.length (List.filter (fun s -> s.k <> Removed) to_do.(codim)))
        trs.nb
        (!nb_single + !nb_multi + !nb_any + !nb_center) !nb_single !nb_multi !nb_any !nb_center
        codim (dim-1) x tail;
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
                    trs.by_edge []
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
              Hashtbl.add simplices k (s.s,s.o.l);
            end;
          (i,j,s.s)
        in
        Hashtbl.add edges k (List.map fn ls)) trs.by_edge;

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
            let x0 = Simp.mkv x0 true in
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
    erase_total ();
    eprintf "total: %d/%d pts:%d=%d+%d+%d+%d,\n   %t,\n   %a\n   %a\n   %a\n"
      keep total
      (!nb_single + !nb_multi + !nb_any + !nb_center)
      !nb_single !nb_multi !nb_any !nb_center
      print_zih_stats
      (print_solver_stats ~name:"solver1") solver1_stat
      (print_solver_stats ~name:"solver2") solver2_stat
      (print_solver_stats ~name:"solver3") solver3_stat;
    let cps = components all in
    let chr = List.map euler cps in
    eprintf "   topology: %d components %a\n%!" (List.length cps) print_int_list chr;
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
                  trs.by_edge []
    in

    restore_objects ();
    (List.map (Array.map to_vec) all, edges)

  let triangulation param p0 =
    let r =
      try
        triangulation param p0
      with Not_found as e ->
        Printexc.print_backtrace stderr;
        eprintf "Uncaught exception %s\n%!" (Printexc.to_string e);
        exit 1
    in
    Chrono.iter (fun n t _ c -> printf "   %10s: %8.3fs for %6d call(s)\n%!" n t c);
    Chrono.reset_all ();
    r

end
