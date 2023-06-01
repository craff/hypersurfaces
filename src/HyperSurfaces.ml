open Debug
open Printing
open Lib

let decomp_log = Debug.new_debug "decomposition" 'd'
let face_log   = Debug.new_debug "face" 'f'

let solver1_chrono = Chrono.create "solver1"
let solver2_chrono = Chrono.create "solver2"
let solver3_chrono = Chrono.create "solver3"
let test_chrono = Chrono.create "test"
let add_chrono = Chrono.create "add"
let certif_chrono = Chrono.create "certif"
let total_chrono = Chrono.create "total"

let chr_solve1 s a b c d = Chrono.add_time solver1_chrono (s a b c) d
let chr_solve2 s a b c d = Chrono.add_time solver2_chrono (s a b c) d
let chr_solve3 s a b c d = Chrono.add_time solver3_chrono (s a b c) d

module Make(R:Field.SPlus) = struct
  open R
  module Simp = Simplices.Make(R)
  module Poly = B
  open B
  open V
  open Simp
  module D = Display.Make(R)
  module Q = Field.Q

  type cert =
    | NZ of (bool array * vector) list
    | SG of int
    | DV of int * int * cert * cert
    | SING

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
    ; dp : polynomial_v list lazy_t
    ; l : R.t array list
    ; c : R.t array
    ; d : R.t
    ; mutable f : float
    ; mutable codim : int
    ; qm : Q.t array array lazy_t
    ; qp : Q.B.polynomial list lazy_t
    ; ql : Q.t array list lazy_t
    ; qdp : Q.B.polynomial_v list lazy_t
    }

  exception Zero

  let fst3 (x,_,_) = x

  let triangulation param p0 =

    let unsafe = ref [] in
    let restore_objects =
      if !Args.prog then Display.hide_all_objects ()
      else (fun () -> ())
    in
    let dims = List.map dim p0 in
    let deg = List.map degree p0 in
    let qp0 = List.map (List.map (fun (m,c) -> (m,to_q c))) p0 in
    let p0 = List.map Poly.normalise p0 in
    let hp0 = List.map to_horner p0 in
    let qhp0 = List.map Q.B.to_horner qp0 in
    let dim = List.hd dims in
    if not (List.for_all ((=) dim) dims) then failwith "inhomogeneous equations";
    let codim = List.length p0 in
    let dp00 = List.map2 (fun p d -> ( pre_eval ( *. ) p
                                    , pre_eval ( **.) (gradient p)
                                    , pre_eval ( ***. ) (hessian p), d)) p0 deg in
    let dp0 = List.filter (fun (_,_,_,d) -> d > 1) dp00 in
    let solver1_stat = init_solver_stats () in
    let solver2_stat = init_solver_stats () in
    let solver3_stat = init_solver_stats () in
    let eval_prod c =
      List.fold_left (fun acc (p,_,_,_) ->
          let n = eval p c in
          acc +. n *. n) zero dp0
    in
    let forbidden = ref [] in
    let single_critical =
      List.map (fun (p,dp,hp,_) ->
         let module F = struct
             let dim = dim
             let fun_min = epsilon2
             let fun_good = small param.Args.crit_limit
             let min_prog_coef = of_int 2
             let min_prog_int = 10*dim
             let lambda_min = epsilon2
             let eval c = fst (eval_tgrad dp c)
             let grad c = fst3 (eval_thess hp c)
             let final c =
               let x = R.B.eval p c in
               let y = grad c in
               let open Stdlib in
               abs_float (to_float (det y)) ** (1.0 /. float dim)
                 /. abs_float (to_float x) > 1e-7
             let dist2 = dist2
             let stat = solver1_stat
             let forbidden = []
           end
         in
         let module S = Solve(F) in
         forbidden := S.solutions :: ! forbidden;
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
               let dim = dim + codim - 1
               let fun_min = epsilon2 *. epsilon2
               let fun_good = small param.Args.crit_limit
	       let final _ = true
               let min_prog_coef = of_int 2
               let min_prog_int = 10*dim
               let lambda_min = epsilon2
               let forbidden = !forbidden
               let dist2 c1 c2 =
                 let r = ref zero in
                 for i = 0 to dim0 - 1 do
                   let d = c1.(i) -. c2.(i) in
                   r := !r +. d *. d
                 done;
                 !r
               let eval c =
                 let x = Array.sub c 0 dim0 in
                 let l = Array.sub c dim0 (codim - 1) in
                 let tg = zero_v dim0 in
                 let ps = zero_v (codim - 1) in
                 List.iteri
                   (fun j (_,dp,_,d) ->
                     let (tg',dp) = eval_tgrad dp x in
                     let p = dp /. of_int d in
                     if j < i then ps.(j) <- p;
                     if j > i then ps.(j-1) <- p;
                     let coef = if j < i then l.(j)
                                else if j = i then one
                                else l.(j-1) in
                     combq one tg coef tg') dp0;
                 Array.init dim (fun j ->
                     if j < dim0 then tg.(j)
                     else ps.(j-dim0))
               let grad c =
                 let x = Array.sub c 0 dim0 in
                 let l = Array.sub c dim0 (codim - 1) in
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
                                 let coef = if m < i then l.(m)
                                            else if m = i then one
                                            else l.(m-1)
                                 in
                                 r := !r +. coef *. th.(j).(k)
                               done;
                               !r
                             end
                           else
                             begin
                               let k' = if k' < i then k' else k' + 1 in
                               let (_,tg,_) = ths.(k') in
                               tg.(j)
                             end
                         else
                           if k < dim0 then
                             begin
                               let j' = if j' < i then j' else j' + 1 in
                               let (_,tg,_) = ths.(j') in
                               tg.(k)
                             end
                           else zero))
               let stat = solver2_stat
           end
         in
         let module S = Solve(F) in
         forbidden := S.solutions :: !forbidden;
         let solve proj check a x =
           let proj' x =
             let x' = proj (Array.sub x 0 dim) in
             let l' = Array.sub x dim (codim - 1) in
             Array.append x' l'
           in
           let check' x =
             let x' = proj (Array.sub x 0 dim) in
             check x'
           in
           let x = Array.init F.dim (fun i ->
                       if i < dim then x.(i) else zero)
           in
           let (fc,r) = S.solve proj' check' a x in
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
              let fun_min = epsilon2 *. epsilon2
              let fun_good = inf
              let min_prog_coef = of_float 10.0
              let min_prog_int = 2*dim
              let lambda_min = epsilon2
              let forbidden = !forbidden
              let eval c =
                let p = penal c in
                let n = fst (eval_tgrad dp c) in
                p **. n
	      let grad c = fst3 (eval_thess hp c)
   	      let final _ = true
              let dist2 = dist2
              let stat = solver3_stat
            end
          in
          let module S = Solve(F) in
          (Any, chr_solve3 S.solve)) dp0
    in

    let nb_single = ref 0 in
    let nb_multi  = ref 0 in
    let nb_any    = ref 0 in
    let nb_center = ref 0 in

    let count_point = function
      | Single -> incr nb_single
      | Multi  -> incr nb_multi
      | Any    -> incr nb_any
      | Center -> incr nb_center
    in

    let module SD = struct
        type t = data simplex
        let compare s1 s2 =
          match compare s2.o.d s1.o.d with
          | 0 -> compare s1.suid s2.suid
          | c -> c
      end
    in

    let module SimpSet = Set.Make(SD) in

    let to_do = Array.make dim SimpSet.empty in

    let ls = quadrants dim in
    let s0 = List.hd ls in
    let qs0 = Array.map (Array.map to_q) s0 in

    let lm =
      List.fold_left (fun acc (ty,solve) ->
          let lm =
            List.flatten (
                List.map
                  (fun s -> pts_in_simplex true s param.Args.crit) ls)
          in
          List.fold_left (fun acc x ->
              try
                let proj = normalise in
                let check _ = () in
                let (fc1,c1) = solve proj check (one /. of_int 1000) x in
                (*                printf "fc1: %a %a\n%!" print fc1 print_ty ty;*)
                let pc = eval_prod c1 in
                (ty,pc,c1,fc1)::acc
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
          distance (Array.map (fun (_,_,c,_) -> c) !lm) i c
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

    let ls = Array.to_list !lm in
    let ls = List.mapi (fun i x -> (i,x)) ls in
    let ls = List.filter (fun (i,(_,_,x,_)) ->
                 i = 0 ||
                 distance (Array.map (fun (_,_,c,_) -> c) !lm) i x > of_float 1e-6) ls in
    let lm = List.map snd ls in
    let lm = Array.of_list lm in


    let lm = if Array.length lm < dim then lm else Array.sub lm 0 dim in
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

    decomp_log.log (fun k -> k "init simplex: %a" print_matrix !lm);

    let lm = Array.map (fun c ->
      Simp.mkv c) !lm
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
    let trs = empty_triangulation dim in

    let nlim = match param.Args.zero_limit with
      | None -> zero
      | Some x -> small x
    in

    let mk ?(f=Stdlib.(1.0 /. float_of_int n)) s =
      let m = Array.map to_vec s in
      let qm = lazy (Array.map (Array.map to_q) m) in
      let p = List.map (fun p -> Poly.transform p s0 m) hp0 in
      let l = List.map (fun p ->
                  let l = plane p in
                  Array.map (fun c -> if abs c <. nlim then zero else c) l) p
      in
      let dp = lazy (List.map (fun p -> gradient p) p) in
      let qp = lazy (let lazy qm = qm in
                     List.map (fun p -> Q.B.transform p qs0 qm) qhp0) in
      let ql = lazy (let lazy qp = qp in
                     List.map Q.B.plane qp) in
      let qdp = lazy (let lazy qp = qp in
                      List.map (fun p -> Q.B.gradient p) qp) in
      let c = V.center m in

      let o = { p; c; d=abs (det m); l; dp; f; codim = 0; qm; qp; ql; qdp } in
      let s = mks ~t:trs o s in
      decomp_log.log (fun k -> k "make %a" print_simplex s);
      s
    in

    let total = ref 0.0 in

    to_do.(0) <- List.fold_left (fun s x -> SimpSet.add (mk x) s)
                   SimpSet.empty ls;

    decomp_log.log (fun k -> k "init simplicies done");
    let add_to_do l =
      to_do.(0) <- List.fold_left (fun s x -> SimpSet.add x s) to_do.(0) l
    in

    let is_vertex m =
      Array.fold_left (fun n m -> if m > 0 then n+1 else n) 0 m = 1
    in

    let plim = small param.Args.pos_limit in

    let positive p =
      let fn (_,c) =
        if c <=. plim then raise Exit
      in
      try List.iter fn p; true with Exit -> false
    in

    let constant_sign2 (l,p) = positive (l ** p) in

    let qpositive p =
      let open Q in
      let ap = ref true in
      let fn (m,c) =
        let t = compare c zero in
        if t < 0 || (is_vertex m && t = 0) then ap := false
      in
      List.iter fn p;
      !ap
    in

    let qconstant_sign2 (l,p) = qpositive Q.B.(l ** p) in

    let sub z dps is =
      List.map (fun dp ->
          let res = ref [] in
          List.iter (fun (m,v) ->
              try
                for i = 0 to dim-1 do
                  if m.(i) <> 0 && not is.(i) then raise Exit;
                done;
                if is_vertex m || v <> z then res := (m,v) :: !res
              with Exit -> ()) dp;
          !res) dps
    in

    let qsub = sub Q.zero in
    let sub = sub zero in

    let sub_v z dps is =
      List.map (fun dp ->
          let res = ref [] in
          List.iter (fun (m,v) ->
              try
                for i = 0 to dim-1 do
                  if m.(i) <> 0 && not is.(i) then raise Exit;
                done;
                if is_vertex m || Array.exists ((<>) z) v then res := (m,v) :: !res
              with Exit -> ()) dp;
          !res) dps
    in

    let qsub_v = sub_v Q.zero in
    let sub_v = sub_v zero in

    let all_gradients vs {s; m; o = {l=l0; _}; _ } =
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
      List.iter (fun (opp,({o={l; _}; m=m'; _})) ->
         let l0 =
           List.map2 (fun deg l ->
               if deg mod 2 = 0 && opp then Array.map (~-.) l else l) deg l
         in
         let l = List.map (fun l -> V.transform l m' m) l0 in
         gd := List.map2 (fun l gd -> l :: gd) l !gd ;
        ) ls;
      (ls,!gd)
    in

    let qall_gradients vs {s; o = {ql= lazy l0;qm= lazy m ; _}; _} =
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
      List.iter (fun (opp,({o={ql=lazy ql;qm=lazy m'; _}; _})) ->
         let l0 =
           List.map2 (fun deg l ->
               if deg mod 2 = 0 && opp then Array.map Q.(~-.) l else l) deg ql
         in
         let l = List.map (fun l -> Q.V.transform l m' m) l0 in
         gd := List.map2 (fun l gd -> l :: gd) l !gd ;
        ) ls;
      (ls,!gd)
    in

    let allowed_error = small param.Args.dprec in

    let visible_v s x =
      let sg, x = if x *.* s.o.c <. zero then (false, opp x) else (true, x) in
      let fn (_,_,d2' as acc) v =
        let d = x --- v in
        let d2 = norm2 d in
        if d2 <. d2' then (false,d,d2) else acc
      in
      let d = x --- normalise s.o.c in
      let d2 = norm2 d in
      let (center,d,_) = Array.fold_left fn (true,d,d2) s.m in
      let v = if center then x *.* s.o.c -. one else d *.* s.o.c in
      (sg, v >. allowed_error)
    in

    let visible s x =
      let x = to_vec x in
      visible_v s x
    in

    let search_points kind allp sd =
      let critical = kind <> Any in
      let select x (_,dy,_,sy,fcy,_ as y) =
        assert (dy >=. zero);
        assert (fcy >=. zero);
        match x with
        | None -> Some y
        | Some (_,dx,_,sx,fcx,_) ->
           if critical then
             match compare (dy*.sx) (dx*.sy) with
             | 1 -> x
             | _ -> Some y
           else
             match compare (fcy*.sx) (fcx*.sy) with
             | 1 -> x
             | _ -> Some y
      in
      let best = ref None in
      let kn (_,s) =
        VectorCommon.sol_log.log (fun k -> k "searching in simplex: %a" print_simplex s);

        let c0 = normalise s.o.c in
        let rs2 =
          if critical then
            let radius2 = dist2 (to_vec s.s.(0)) c0 in
            radius2 *. of_float 1e-10
          else -. one
        in
        let fn best (ty,solve) c0 =
          try
            (*if not critical then printf "solve %a %a ==> " print_vector s.c print_vector c0;*)
            let proj =
              if critical then normalise
              else
                let coef = ((norm s.o.c -. one) *. of_float 0.9 +. one) /. norm s.o.c in
                assert (coef >. zero);
                let cen = coef **. s.o.c in
                project_circle cen 0.05
            in
            let check =
              if critical then
                (fun c ->
                let d = c *.* s.o.c in
                if d <. of_float 0.9 then raise V.Abort)
              else fun _ -> ()
            in
            let (fc1,c1) = solve proj check rs2 c0 in
            assert(fc1 >=. zero);
            let (b1,b2) = visible_v s c1 in
            (*if not critical then printf "fc1: %a %a %b %b\n%!" print fc1 print_ty ty b1 b2;*)
            if not b1 || not b2 then
              begin
                VectorCommon.sol_log.log (fun k -> k "reject %b %b %b" b1 b2 (fc1 >. epsilon));
                raise Not_found
              end;
            let p2 = eval_prod c1 in
            let md2 = Array.fold_left (fun md2 x ->
                          let d2 = min (dist2 x c1) (dist2 (opp x) c1) in min md2 d2) inf s.m
            in
            select best (s, p2, c1, md2, fc1, ty)
          with Not_found -> (*printf "NF\n%!";*) best
        in
        List.iter (fun solve ->
            let nb = param.Args.crit in
            let lm =
              if critical && nb > 1 then pts_in_simplex false s.m nb
              else [s.o.c]
            in
            List.iter (fun c -> best := fn !best solve c) lm) allp
      in
      List.iter kn sd;
      let (s, c, ty) = match !best with
        | None -> VectorCommon.sol_log.log (fun k -> k "keep nothing"); raise Not_found
        | Some (s, _, c, sc, fc, ty) ->
           VectorCommon.sol_log.log (fun k -> k "keep %a with sc: %a, fc: %a"
             print_vector c print sc print fc;
(*           if not critical then printf "keep %a with sc: %a, fc: %a\n%!"
             print_vector c print sc print fc;*));
           (s, c, ty)
      in
      (s, Simp.mkv c, ty)
    in

    let search_single_critical sd =
      VectorCommon.sol_log.log (fun k -> k "start search critical");
      search_points Single single_critical sd
    in
    let search_multi_critical sd =
      VectorCommon.sol_log.log (fun k -> k "start search multi critical");
      search_points Multi multi_critical sd
    in
    let search_penal_critical c sd =
      VectorCommon.sol_log.log (fun k -> k "start search penal");
      search_points Any (penal_critical c) sd
    in

    let open struct exception Zih of vector * vector list * (bool * simplicies) list end in

    let is_small = R.pow (small param.Args.safe) (dim-1) in

    let certs = Hashtbl.create 1024 in

    let zlim = small param.Args.zih_limit in

    let slim = match param.Args.sing_limit with
      | None -> zero
      | Some x -> small x
    in

    let decision_face codim vs (s as s0) =
      let (sd,gd) = all_gradients vs s in
      let adone = List.exists (fun (_,s) -> assert(s.k <> Removed);
                                            s.o.codim > codim) sd
      in
      face_log.log (fun k -> k "decision for %a, adone: %b\n%!" print_matrix s.m adone);
      if not adone then
      let too_hard = List.exists (fun (_,s) ->
                         s.o.d < is_small &&
                           (unsafe := s :: !unsafe; true)) sd
      in
      if not too_hard then
      let p = sub s.o.p vs in
      let nb_vs = Array.fold_left (fun x b -> if b then x+1 else x) 0 vs in
      let l = List.map first_deg p in
      let dp = sub_v (Lazy.force s.o.dp) vs in
      let rec kn subd s l p dp =
        let lp = List.combine l p in
        let cst = find_i constant_sign2 lp in
        match cst with
        | Some i -> face_log.log (fun k -> k "constant sign"); SG i
        | _ -> hn subd s l p dp
      and hn subd s l p dp =
        (*        printf "l:%a p:%a\n%!" (print_polynome ?vars:None) (List.hd l) (print_polynome ?vars:None) (List.hd p);*)
        (*        printf "cst: %b, subd: %d %a\n%!" cst subd print_matrix s;*)
        let rec fn acc signs points dps gds =
          match (dps, gds) with
          | [], [] ->
             begin
               let signs = Array.of_list (List.rev signs) in
               match zih zlim points with
               | None   -> face_log.log (fun k -> k "test zih: true"); InL points
               | Some v -> face_log.log (fun k -> k "test zih: false");
                           InR ((signs, v)::acc)
             end
          | dp::dps, gd::gds ->
             let dp = List.map snd dp in
             let new_points = dp @ gd in
             let new_points = List.filter (fun g -> not (norm2 g <. slim)) new_points in
             (match fn acc (true::signs) (new_points @ points) dps gds with
              | InR acc when dps <> [] ->
                 let new_points = List.map opp new_points in
                 fn acc (false::signs) (new_points @ points) dps gds
              | r    -> r)
          | _ -> assert false
        in
        let res = fn [] [] [] dp gd in
        match res with
        | InR v -> NZ v
        | InL all when subd <= 0 || nb_vs = 1 ->
           begin
             try
               face_log.log (fun k -> k "face not good, stops");
               let l = ref [] in
               Array.iteri (fun i x -> if vs.(i) then l:= x :: !l) s0.m;
               let p = normalise (lcenter (Array.of_list !l)) in
               raise (Zih (p,all,sd))
             with Not_found -> assert false
           end
        | InL _ ->
           begin
             let best = ref (-.one, (-1,-1)) in
             for i = 1 to dim - 1 do
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
             face_log.log (fun k -> k "subdivise %d %d, first test" i j);
             let c1 = kn (subd-1) s1 l1 p1 dp1 in
             face_log.log (fun k -> k "subdivise %d %d, second test" i j);
             let c2 = kn (subd-1) s2 l2 p2 dp2 in
             DV (i,j,c1,c2)
           end
      in
      if codim = 0 && List.exists (Array.for_all ((=.) zero)) s.o.l then
        raise Zero;
      let cert =
        if codim > 0 &&
             List.exists (List.for_all (fun (_,g) -> norm2 g <. slim)) dp then
          SING
        else
          kn param.Args.subd s.m l p dp
      in
      let key = facet_key s.s vs in
      Hashtbl.replace certs key (s,cert,ref false)
    in

    let check_decision_face vs s' s cert =
      assert (s.k <> Removed);
      assert (s'.k <> Removed);
      let (sd,gd) = qall_gradients vs s in
      assert (List.exists (fun (_,c) -> s.suid = c.suid) sd);
      assert (List.exists (fun (_,c) -> s'.suid = c.suid) sd);
      let p : Q.B.polynomial list = qsub (Lazy.force s.o.qp) vs in
      let l : Q.B.polynomial list = List.map Q.B.first_deg p in
      let dp = qsub_v (Lazy.force s.o.qdp) vs in
      let rec kn subd s (l: Q.B.polynomial list) p dp cert =
        match cert with
        | SING -> ()
        | SG i ->
           let ((l,p) as lp) = List.nth l i, List.nth p i in
           if not (qconstant_sign2 lp) then
             begin
               eprintf "%a\n" (Q.B.print_polynome ~times:false ~q:false ?vars:None) Q.B.(l ** p);
               failwith "bad certificate: polynomials not of constant signs"
             end;
        | NZ ls ->
           let rec fn signs points dps gds =
             match (dps, gds) with
             | [], [] ->
                let signs = Array.of_list (List.rev signs) in
                let v =
                  try
                    Array.map to_q (List.assoc signs ls)
                  with Not_found -> assert false
                in
                List.iter (fun w ->
                    let s = Q.V.(v *.* w) in
                    let v = Array.map Q.to_float v in
                    let w = Array.map Q.to_float w in
                    if Q.(s <=. zero) then
                      failwith (sprintf "bad certificate: zero in hull (%e <= 0) (%a.%a)"
                                  (Q.to_float s)
                                  Field.Float.V.print_vector v
                                  Field.Float.V.print_vector w)) points
             | dp::dps, gd::gds ->
                let dp = List.map snd dp in
                let new_points = dp @ gd in
                fn (true::signs) (new_points @ points) dps gds;
                if dps <> [] then
                  let new_points = List.map Q.V.opp new_points in
                  fn (false::signs) (new_points @ points) dps gds
             | _ -> assert false
           in
           fn [] [] dp gd
        | DV (i,j,c1,c2) ->
           assert (i >= 0 && j >= 0 && i <> j);
           (*                 printf "split %d %d\n%!" i j;*)
           let l1,l2 =
             List.split (List.map (fun p -> Q.B.subdivise p i j) l) in
           let p1,p2 =
             List.split (List.map (fun p -> Q.B.subdivise p i j) p) in
           let dp1,dp2 =
             List.split (List.map (fun p -> Q.B.subdivise_v p i j) dp) in
           let s1 = Array.mapi (fun k x ->
                        if k = j then (x +++ s.(i)) //. of_int 2 else x) s in
           let s2 = Array.mapi (fun k x ->
                        if k = i then (x +++ s.(j)) //. of_int 2 else x) s in
           kn (subd-1) s1 l1 p1 dp1 c1;
           kn (subd-1) s2 l2 p2 dp2 c2
      in
      kn param.Args.subd s.m l p dp cert
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
                if old < dim then
                  to_do.(old) <- SimpSet.remove s' to_do.(old);
                s'.o.codim <- codim;
                if codim < dim then
                  to_do.(codim) <- SimpSet.add s' to_do.(codim);
                total := Stdlib.(!total -. float (old - codim) *. s'.o.f);
              end) l
      done;
    in

    let decision codim s =
      try
        let fn (_,vs) =
          decision_face codim vs s
        in
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
        List.iter fn facets;
        NonDege
      with
      | Zih (v,all,sd) -> Depend (v,all,(true,s)::sd)
      | Zero -> Depend(s.o.c,[],[true,s])
      | e -> eprintf "got except: %s\n%!" (Printexc.to_string e);
                assert false
    in

    let ajoute s x = Chrono.add_time add_chrono (fun ty ->
      assert (s.k = Active);
      let (sg, v) = visible s x in
      assert ((v && sg) ||
        let x = to_vec x in
        let m = Array.map (fun p -> p --- x) s.m in
        let m' = Array.map (fun p -> p +++ x) s.m in
        printf "\nx(%b,%b,%a): %a(%a)\nc: %a(%a)\ns:%a => %a\n%a => %a\n%a => %a\n%!"
          sg v print_ty ty
          print_vector x print (norm2 x)
          print_vector s.o.c print (x *.* s.o.c -. one)
          print_matrix s.m print_vector (Array.map (fun x -> x *.* s.o.c -. one) s.m)
          print_matrix m print (det m)
          print_matrix m' print (det m');
        false);
      total := Stdlib.(!total -. float s.o.codim *. s.o.f);
      count_point ty;
      rm trs s;
      if s.o.codim < dim then
        to_do.(s.o.codim) <- SimpSet.remove s to_do.(s.o.codim);
      decomp_log.log (fun k ->
          k "adding center %a to %a (%a => %a)"
            print_vector (to_vec x)
            print_simplex s print_vector s.o.c print (s.o.c *.* (to_vec x)));
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
        decomp_log.log (fun k -> k "%d+%d faces" (List.length l) (List.length acc));
        match l with
        | []       -> (acc,area)
        | (i,s,key as c)::l ->
           decomp_log.log (fun k -> k "test face %d of %a\ntest with key %a"
             i print_simplex s print_face_key key);
           assert (s.k = Removed);
           let l0 = try Hashtbl.find trs.by_face key with Not_found -> [] in
           let (sg,v)   = visible s  x in
           assert v;
           match l0 with
           | [(j,s')] ->
              decomp_log.log (fun k -> k "next simplex tested is %a" print_simplex s');
              let (sg',v') = visible s' x in
              assert(s'.k <> Removed);
              if v' then
                begin
                  let i0 = if i = 0 then 1 else 0 in
                  let j0 = ref 0 in
                  while s'.s.(!j0).uid <> s.s.(i0).uid do incr j0 done;
                  let j0 = !j0 in
                  decomp_log.log (fun k -> k "to remove");
                  let good = (sg = sg') = (s.s.(i0).p = s'.s.(j0).p) in
                  let acc = ref acc in
                  let l   = ref l   in
                  total := Stdlib.(!total -. float s'.o.codim *. s'.o.f);
                  rm trs s';
                  if s'.o.codim < dim then
                    to_do.(s'.o.codim) <- SimpSet.remove s' to_do.(s'.o.codim);
                  Array.iteri (fun k _ ->
                      if k <> j then
                        begin
                          let key' = face_key s'.s k in
                          let (b,l')  = rml [] key' !l   in
                          match b with
                          | None ->
                             decomp_log.log (fun kk ->
                                 kk "adding face %d of %a" k print_simplex s');
                             l := (k,s',key') :: l'
                          | Some(h,s'',_) ->
                             l := l';
                             let h0 = if h = 0 then 1 else 0 in
                             let j0 = ref 0 in
                             while s'.s.(!j0).uid <> s''.s.(h0).uid do incr j0 done;
                             let j0 = !j0 in
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
              decomp_log.log (fun k -> k "len: %d for %a\n%!"
                                     (List.length l0) print_face_key key);
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
            decomp_log.log (fun k -> k "before mk");
            let r = mk ~f:area s' in

            decomp_log.log (fun k -> k "after mk");
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
      o.Display.visible <- true;
      tmp_object := Some o
    in

    let test codim =
      let ls = to_do.(codim) in
      to_do.(codim) <- SimpSet.empty;
      let fn s =
        if s.k <> Removed && s.o.codim = codim then
        let d = Chrono.add_time test_chrono (decision codim) s in
        match d with
        | NonZero | NonDege ->
           total := Stdlib.(!total +. s.o.f);
           s.o.codim <- s.o.codim + 1;
           if s.o.codim < dim then
             to_do.(s.o.codim) <- SimpSet.add s to_do.(s.o.codim);
        | Depend(_,_,sd) ->
           assert (s.k = Active);
           if List.exists (fun (_,s) -> s.k = Removed) sd then
             to_do.(s.o.codim) <- SimpSet.add s to_do.(s.o.codim)
           else
             begin
               try
                 assert (List.for_all (fun (_,s) -> s.k = Active) sd);
                 let (s,c,ty) = search_single_critical sd in
                 assert (s.k = Active);
                 ajoute s c ty;
               with Not_found -> try
                 assert (List.for_all (fun (_,s) -> s.k = Active) sd);
                 let (s,c,ty) = search_multi_critical sd in
                 assert (s.k = Active);
                 ajoute s c ty
               with Not_found -> try
                 assert (List.for_all (fun (_,s) -> s.k = Active) sd);
                 let (s,c,ty) = search_penal_critical s.o.c sd in
                 assert (s.k = Active);
                 ajoute s c ty
               with Not_found ->
                 assert (s.k = Active);
                 VectorCommon.sol_log.log (fun k -> k "take center");
                 let c = normalise s.o.c in
                 let c = Simp.mkv c in
                 ajoute s c Center
             end;
      in SimpSet.iter fn ls
    in

    let print_total codim =
      let x = match SimpSet.max_elt_opt to_do.(codim) with
        | None   -> 0.0
        | Some s -> to_float s.o.d
      in
      let (hd,tail) = if Debug.has_debug () then "", "\n" else "\r", "" in
      eprintf "%s%6.3f%% %06d/%06d pts:%2d=%2d+%2d+%2d+%2d, codim: %d/%d, worst:%5.2e%s%!"
        hd Stdlib.(!total *. 100.0 /. float dim)
        (SimpSet.cardinal to_do.(codim))
        trs.nb
        (!nb_single + !nb_multi + !nb_any + !nb_center) !nb_single !nb_multi !nb_any !nb_center
        codim (dim-1) x tail;
    in

    let erase_total () =
      let str = String.make 79 ' ' in
      eprintf "\r%s\r" str
    in

    while not (Array.for_all SimpSet.is_empty to_do) do
      let codim =
        let res = ref 0 in
        try
          for i = 0 to dim-1 do
            res := i; if not (SimpSet.is_empty to_do.(i)) then raise Exit
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

    let check () =
      eprintf "check that points are not visible from other simplex\n%!";
      Hashtbl.iter (fun _ l ->
          let v = match l with
            | [] -> assert false
            | (i,s)::_-> s.s.(i)
          in
          Hashtbl.iter (fun _ s' ->
              assert (List.exists (fun (_,s) -> s.suid = s'.suid) l ||
                        not (snd (visible s' v)))) trs.all) trs.by_vertex;
      eprintf "check two simplex by faces of opposite side\n%!";
      Hashtbl.iter (fun _ l ->
          match l with
          | [(i,s);(j,s')] ->
             let m1 = s.m in
             let v = s'.s.(j) in
             let i0 = if i = 0 then 1 else 0 in
             let j0 = ref (-1) in
             for l = 0 to dim - 1 do
               if s'.s.(l).uid = s.s.(i0).uid then j0 := l
             done;
             assert (!j0 >= 0);
             let v = if s'.s.(!j0).p = s.s.(i0).p then v else ch_sg v in
             let m2 = Array.mapi (fun k x -> if k = i then to_vec v else x) m1 in
             assert (det m1 *. det m2 <. zero);
          | _ -> assert false) trs.by_face
    in
    if param.Args.check then check ();

    let (nb, eps) = match param.Args.project with
      | None -> (0, zero)
      | Some(nb,e) -> (nb, of_float e)
    in

    let s1 =
      let s0 x =
        let x2 = norm2 x in
        assert (x2 <. one);
        exp (-. one /. (one -. x2))
      in
      let n = ball_integrals s0 dim 10 in
      fun x -> s0 x /. n
    in

    let find_simplex x =
      let r = ref [] in
      Hashtbl.iter (fun _ s ->
          let c = pcoord x s.m in
          let inside = Array.for_all (fun x -> x >=. -. of_float 1e-24) c in
          if inside then r:= (s,c,true) :: !r;
          let c = pcoord (opp x) s.m in
          let inside = Array.for_all (fun x -> x >=. -. of_float 1e-24) c in
          if inside then r:= (s,c,false) :: !r;
        ) trs.all;
      match !r with
      | [] -> assert false
      | _ -> !r
    in

    let zerov = zero_v codim in
    let zerom = zero_m codim dim in

    let phat x0  =
      (*printf "phat: %a = %!" print_vector x;*)
      let l = find_simplex x0 in
      let fn (s,x,sg) =
        let sg deg = if not sg && deg mod 2 = 0 then -. one else one in
        let p = List.map2 (fun l deg ->
                    let dp = l *.* x in
                    R.pow (norm x0) (deg-1) *. sg deg *. dp) s.o.l deg in
        let r =
          Array.of_list p
        in
        r
      in
      let l = List.map fn l in
      let n = List.length l in
      (List.fold_left (+++) zerov l) //. of_int n
    in

    let gphat x0  =
      let l = find_simplex x0 in
      let fn (s,x,sg) =
        let sg deg = if not sg && deg mod 2 = 0 then -. one else one in
        let m = List.map2 (fun l deg ->
                    let dp = l *.* x in
                    let x1 = R.pow (norm x0) (deg-1) *. sg deg in
                    let l1 = V.transform l s.m s0 in
                    let x2 = dp *. of_int (deg-1) *. R.pow (norm x0) (deg-3) *. sg deg in
                    x1 **. l1 +++ x2 **. x0
                  (* ignore derivative of x power as it is normal *)
                  ) s.o.l deg
        in
        Array.of_list m
      in
      let l = List.map fn l in
      let n = List.length l in
      let r =
        (one /. of_int n) ***. (List.fold_left (fun acc x -> x ++++ acc) zerom l)
      in
(*      let d = Array.init dim (fun _ -> of_float (Random.float 1.0)) in
      let d = normalise d in
      let v = phat x0 in
      let eps = eps *. of_float 1e-3 in
      let v' = phat (x0 +++ eps **. d) in
      let e = (v' --- v) //. eps --- (r *** d) in
      printf "x0: %a, gphat: %a\n%!" print_vector x0 print_matrix r;
      printf "ERR: %a (%d)\n%!" print_vector e n;*)
      r
    in

    let sphat t x =
      let f u = s1 u **. phat (x --- (t *. eps) **. u) in
      ball_integrals1 zerov f dim nb
    in

    let dsphat_dt t x =
      let f u = (-. eps *. s1 u) **. (gphat (x --- (t *. eps) **. u) *** u) in
      ball_integrals1 zerov f dim nb
    in

    let gsphat t x =
      let f u = s1 u ***. gphat (x --- (t *. eps) **. u) in
      let r =  ball_integrals2 zerom f dim nb in
      (*printf "  gsphat: %a\n%!" print_matrix r;*)
      r
    in

    let pt t x =
      let p = Array.of_list (List.map (fun (p,_,_,_) -> eval p x) dp00) in
      let q = sphat t x in
      (one -. t) **. q +++ t **. p
    in

    let q t x =
      let v1 = Array.of_list (List.map (fun (p,_,_,_) -> eval p x) dp00) in
      let v2 = sphat t x in
      let v3 = dsphat_dt t x in
      v1 --- v2 +++ (one -. t) **. v3
    in

    let g t x =
      let m1 = Array.of_list (List.map (fun (_,dp,_,_) -> eval_grad dp x) dp00) in
      let m2 = gsphat t x in
      let r = (t ***. m1) ++++ ((one -. t) ***. m2) in
      let r = Array.map (fun r -> r --- ((r *.* x) /. norm2 x) **. x) r in
      r
    in

    let f t x =
      let g = g t x in (* codim lines of dim length *)
      let gg = g **** transpose g in
      let q = q t x in
      try
        let r = (-.one) **. (transpose g *** (solve gg q))in
        r
      with Not_found -> failwith "g not invertible"
    in

    let isotopy x =
      let debug t x =
        let eps = eps *. of_float 1e-4 in
        let v = pt t x in
        let v' = pt (t +. eps) x in
        let e = (v' --- v) //. eps --- q t x in
        let d = Array.init dim (fun _ -> of_float (Random.float 1.0)) in
        let d = d --- (d *.* x /. norm2 x) **. x in
        let d = normalise d in
        let v' = pt t (x +++ eps **. d) in
        let m = g t x in
        let e' = (v' --- v) //. eps --- (m *** d) in
        printf "t: %a, x: %a, pt: %a (%a %a %d %d)\n%!"
          print t print_vector x print_vector v
          print_vector e print_vector e' (Array.length m) (Array.length m.(0))
      in
      let x = rk4_1 ~debug f zero eps x 1 in
      rk4_1 ~debug f eps one x (nb*50)
    in

    let ctrs = empty_triangulation ~has_v_tbl:false ~has_f_tbl:false dim in

    Hashtbl.iter (fun _ s -> add ctrs (mks s.o.l s.s)) trs.all;

    let rec extract dim codim trs =
      let edge_value l =
        match l with
        | [] -> assert false
        | (i,j,s)::_ ->
(*           printf "testing %a %a\n%!" print_vector (to_vec s.(i))
             print_vector (to_vec s.(j));*)
           match s.o with
           | [] -> assert false
           | v :: _ ->
              (s.s.(i), v.(i), s.s.(j), v.(j))
      in
      let split_edge k =
        let l = try Hashtbl.find trs.by_edge k with Not_found -> assert false in
        let (si,xi,sj,xj) = edge_value l in
        if xi *. xj <. zero then
          begin
            let d = xj -. xi in
            let (t,u) = (xj /. d, -. xi /. d) in
            assert (t >. zero);
            assert (u >. zero);
            let x0 = comb t (to_vec si) u (to_vec sj) in
            (*printf "splitting %d: %a\n%!" codim print_vector x0;*)
            let x0 = Simp.mkv x0 in
            let fn (i,j,s) =
              assert (s.k = Active);
              assert (s.s.(i).uid = si.uid);
              assert (s.s.(j).uid = sj.uid);
              let sign = s.s.(i).p = si.p in
              assert (sign = (s.s.(j).p = sj.p));
              let x0 = if sign then x0 else ch_sg x0 in
              let l = s.o in
              let s1 = Array.mapi (fun k x -> if i = k then x0 else x) s.s in
              let s2 = Array.mapi (fun k x -> if j = k then x0 else x) s.s in
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
              rm trs s;
              add trs (mks l1 s1);
              add trs (mks l2 s2);
            in
            List.iter fn l;
          end
      in

      let ls = ref [] in
      Hashtbl.iter (fun k _ -> ls := k :: !ls) trs.by_edge;
      List.iter split_edge !ls;

      let new_trs = empty_triangulation ~has_v_tbl:(codim=1) ~has_f_tbl:false dim in

      let collect _ s0 =
        let l = s0.o and s = s0.s in
        let (keep, l) = match l with
          | [] -> assert false
          | v::ls ->
             let l = ref [] in
             Array.iteri (fun i x -> if x =. zero then l := i::!l) v;
             (List.rev !l, ls)
        in
        let keep = Array.of_list keep in
        let nb_keep = Array.length keep in
        let fn keep =
          let s = Array.map (fun i -> s.(i)) keep in
          let l = List.map (fun v ->
                      Array.map (fun i -> v.(i)) keep) l in
          if not (Hashtbl.mem new_trs.all (simplex_key s))
          then add new_trs (mks l s)
        in
        if nb_keep = dim then fn keep
(*        else if nb_keep = dim+1 then
          begin
            printf "STRANGE\n%!";
            for i = 0 to dim do
              let keep =
                Array.init dim (fun j -> keep.(if j < i then j else j+1))
              in
              fn keep
            done
          end*)
        else assert (nb_keep < dim || (
               printf "%d < %d\n%!" nb_keep dim; false))
      in

      Hashtbl.iter collect trs.all;

      let dim = dim - 1 in
      let codim = codim - 1 in
      if codim > 0 then
        begin
          extract dim codim new_trs
        end
      else
        new_trs
    in
    erase_total ();
    eprintf "\rExtracting simplicies.%!";
    let codim = List.length p0 in
    let ctrs = extract (dim-1) codim ctrs in
    let tbl = Hashtbl.create 1024 in
    let fn s =
      try let (v,p) = Hashtbl.find tbl s.uid in
          if s.p = p then v else ch_sg v
      with Not_found ->
            let x = isotopy (to_vec s) in
            let v = mkv x in
            Hashtbl.add tbl s.uid (v,s.p);
            v
    in
    let ptrs = ref [] in
    if param.Args.project <> None then
      Hashtbl.iter (fun _ s ->
          let s = Array.map fn s.s in
          ptrs := s :: !ptrs) ctrs.all;

    let all =
      let all = ref [] in
      Hashtbl.iter (fun _ s ->
          assert (s.o=[]);
          all := s.s :: !all) ctrs.all;
      !all
    in

    eprintf "\rtotal: %d/%d pts:%d=%d+%d+%d+%d,\n   %t,\n   %a\n   %a\n   %a\n"
      ctrs.nb trs.nb
      (!nb_single + !nb_multi + !nb_any + !nb_center)
      !nb_single !nb_multi !nb_any !nb_center
      print_zih_stats
      (print_solver_stats ~name:"solver1") solver1_stat
      (print_solver_stats ~name:"solver2") solver2_stat
      (print_solver_stats ~name:"solver3") solver3_stat;

    let nb_unsafe = List.length !unsafe in

    let edges = Hashtbl.fold (fun _ l acc ->
                    match l with
                    | [] -> assert false
                    | (i,j,s)::_ -> [|s.m.(i); s.m.(j)|]::acc)
                  trs.by_edge []
    in

    restore_objects ();

    let check_certif () =
      let facets = enum_facets None dim in
      let nb = Hashtbl.length trs.all in
      let checked = ref 0 in
      let idxs = List.init dim (fun i -> i) in
      Hashtbl.iter (fun _ s ->
          List.iter (fun vs ->
              let key = facet_key s.s vs in
              try
                let (s',cert,checked) = Hashtbl.find certs key in
                if not !checked then
                  begin
                    let vs =
                      Array.init dim (fun i ->
                          try
                            let j =
                              List.find (fun j -> s.s.(j).uid = s'.s.(i).uid) idxs
                            in
                            vs.(j)
                          with Not_found -> false
                        )
                    in
                    check_decision_face vs s s' cert;
                    checked := true
                  end
              with Not_found -> assert false) facets;
          incr checked;
          eprintf "\rchecking certificate: %.2f%%   %!"
            Stdlib.(float !checked /. float nb *. 100.)
        ) trs.all;
      eprintf "\rcertificate OK                                 \n%!"
    in

    if param.Args.certif && nb_unsafe = 0 then
      Chrono.add_time certif_chrono check_certif ()
    else
      if param.Args.certif then
        eprintf "unsafe cells present: not checking certificate\n%!";

    (List.map (Array.map to_vec) all, List.map (Array.map to_vec) !ptrs
     , edges, dim, ctrs, nb_unsafe = 0)

  let triangulation param p0 =
    let (all,ptrs,edges,dim,ctrs,unsafe) =
      try
        Chrono.add_time total_chrono (triangulation param) p0
      with Not_found as e ->
        Printexc.print_backtrace stderr;
        eprintf "Uncaught exception %s\n%!" (Printexc.to_string e);
        exit 1
    in
    let r = (all,ptrs,edges,dim,ctrs,unsafe,Chrono.get_cumul total_chrono) in
    Chrono.iter (fun n t tc c -> printf "   %10s: %8.3fs (%8.3fs self) for %6d call(s)\n%!" n tc t c);
    Chrono.reset_all ();
    r

end
