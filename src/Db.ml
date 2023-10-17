open Sqlite3
open Format
open Debug

let db_log = Debug.new_debug "db" 'q'

let create_polynomial = {|
  CREATE TABLE IF NOT EXISTS polynomial (
    value TEXT PRIMARY KEY,
    degree INTEGER,
    dimension INTEGER,
    random INT(1))|}

let rec pkey n = match n with
  | _ when n <= 0 -> assert false
  | 1             -> "p0 INTEGER"
  | n             -> sprintf "%s, p%d INTEGER" (pkey (n-1)) (n-1)

let create_variety n = sprintf {|
  CREATE TABLE IF NOT EXISTS variety%d (
    %s,
    nb_components INTEGER,
    topology TEXT,
    time FLOAT,
    subd INTEGER,
    crit INTEGER,
    crit_limit FLOAT,
    pos_limit FLOAT,
    zih_limit FLOAT,
    dprec FLOAT
   )|} n (pkey n)
   (* euler : list of integers as string *)

let db_ptr = ref None
let db () =
  match (!db_ptr, !Args.dbname) with
  | (Some db, _     ) -> db
  | (None, None     ) -> assert false
  | (None, Some name) ->
     try
       let db = db_open ~mutex:`FULL ~cache:`PRIVATE name in
       Rc.check (exec db create_polynomial);
       db_ptr := Some db;
       db_log.log (fun k -> k "data base %s created" name);
       let init = (0.0,0.0,0) in
       let open Data in
       let step (m,v,n as acc) x =
         let x,c =
           match x with FLOAT x -> (x,1)
                      | INT x -> (Int64.to_float x,1)
                      | _ -> (0.0,0)
         in
         let n = n + c in
         if c > 0 then
           let e = x -. m in
           let m' = m +. e /. float n in
           let v = v +. e *. (x -. m') in
           (m',v,n)
         else acc
       in
       let final (_,v,n) =
         FLOAT (sqrt (v/. float n))
       in
       let _ = Aggregate.create_fun1 db "STD" ~init ~step ~final in
       db
     with
     | SqliteError s | Error s ->
        eprintf "can not create data base %s for statistics: %s\n%!" name s;
        exit 1


let insert_polynomial to_str p deg dim rand =
  let sql = sprintf "SELECT rowid FROM polynomial WHERE value = '%a'"
              to_str p
  in
  let res = ref None in
  let cb row _ =
    assert (Array.length row = 1);
    (* printf "got %s\n%!" row.(0);*)
    res := Some (Int64.of_string row.(0))
  in
  Rc.check (exec_not_null (db ()) ~cb sql);
  match !res with
  | Some pid -> pid
  | None ->
     let sql =
       sprintf
         "INSERT INTO polynomial VALUES ('%a',%d,%d,%d)"
         to_str p deg dim
         (if rand then 1 else 0)
     in
     try
       Rc.check (exec (db ()) sql);
       last_insert_rowid (db ())
     with
       SqliteError s ->
       eprintf "can not insert polynomial: %s %s\n%!" s sql;
       exit 1

let insert_variety to_str ps dim nbc topo time opts =
  try
    let open Args in
    let nb_pol = List.length ps in
    Rc.check (exec (db ()) (create_variety nb_pol));
    let pid =
      List.map (fun (p,deg,rand) ->
          (deg, insert_polynomial to_str p deg dim rand)
        ) ps
    in
    let pid = List.map snd (List.sort compare pid) in
    let pid_sel = String.concat " AND " (List.mapi (sprintf "p%d = %Ld") pid) in
    let sql =
      sprintf
        "SELECT nb_components, topology, time FROM variety%d WHERE %s"
        nb_pol pid_sel
    in
    let res = ref None in
    let cb row _ =
      assert (Array.length row = 3);
      res := Some (int_of_string row.(0), row.(1), float_of_string row.(2))
    in
    Rc.check (exec_not_null (db ()) ~cb sql);
    match !res with
    | Some (nbc', topo',time') ->
       let topo' = Topology.of_string topo' in
       if nbc' <> nbc || not (Topology.agree topo topo') then
         begin
           eprintf "TOPOLOGY DISAGREE: %a %a"
             Topology.print topo Topology.print topo';
           exit 1
         end;
       let better_topo = Topology.better topo topo' in
       if time < time' || better_topo then
         begin
           let time = min time time' in
           let topo = Topology.(to_string (if better_topo then topo else topo')) in
           let sql =
             sprintf "UPDATE variety%d SET topology='%s',time=%E,subd=%d,crit=%d,crit_limit=%E,pos_limit=%E,zih_limit=%E,dprec=%E WHERE %s"
               nb_pol topo time opts.subd opts.crit
               opts.crit_limit opts.pos_limit opts.zih_limit opts.dprec
               pid_sel
           in
           db_log.log (fun k -> k "%s" sql);
           Rc.check (exec (db ()) sql);
         end
    | None ->
       let pid_ins = String.concat "," (List.map Int64.to_string pid) in
       let topo = Topology.to_string topo in
       let sql =
         sprintf "INSERT INTO variety%d VALUES (%s,%d,'%s',%E,%d,%d,%E,%E,%E,%E)"
           nb_pol pid_ins nbc topo time
           opts.subd opts.crit
           opts.crit_limit opts.pos_limit opts.zih_limit opts.dprec
       in
       db_log.log (fun k -> k "%s" sql);
       Rc.check (exec (db ()) sql);
  with
    SqliteError s ->
     eprintf "can not insert variety: %s\n%!" s;
     exit 1

let timings ?(css=false) dim nb =
  let pols =
    let rec fn n =
      if n < 0 then ""
      else sprintf "%s, polynomial as p%d" (fn (n-1)) n
    in
    fn (nb-1)
  in
  let degs =
    List.init nb (fun i -> sprintf "p%d.degree" i)
  in
  let degs = String.concat ", " degs in
  let where =
    List.init nb (fun i ->
        sprintf
          "v.p%d = p%d.rowid AND p%d.dimension = %d AND p%d.random = 1"
          i i i dim i)
  in
  let where = String.concat " AND " where in
  let sql =
    sprintf
      {|SELECT p0.dimension, %s, AVG(v.time), STD(v.time), MAX(v.time), COUNT() FROM variety%d as v%s WHERE %s
        GROUP BY p0.dimension, %s|}
      degs nb pols where degs
  in
  db_log.log (fun k -> k "sql: %s" sql);
  let res = ref [] in
  let cb row _ =
    res := row :: !res;
  in
  Rc.check (exec_not_null (db ()) ~cb sql);
  List.iter (fun row ->
      let dim = int_of_string row.(0) in
      let degs = Array.init nb (fun i -> int_of_string row.(i+1)) in
      let time = float_of_string row.(nb+1) in
      let std = float_of_string row.(nb+2) in
      let max = float_of_string row.(nb+3) in
      let nb = int_of_string row.(nb+4) in
      let (format, pr) : ('a,'b,'c,'d) format4 * 'e =
        if css then
          "%d, %a, %f, %f, %f, %d\n", Printing.print_int_array_np
        else
          "%d, %a => %.4fs [%.4fs] < %.4fs (%d samples)\n", Printing.print_int_array
      in
      printf format dim pr degs time std max nb) !res

let stats dim degs =
  let degs = List.sort compare degs in
  let nb = List.length degs in
  let pols =
    let rec fn n =
      if n < 0 then ""
      else sprintf "%s, polynomial as p%d" (fn (n-1)) n
    in
    fn (nb-1)
  in
  let where =
    List.mapi (fun i deg ->
        sprintf
          "v.p%d = p%d.rowid AND p%d.dimension = %d AND p%d.degree = %d AND p%d.random = 1"
          i i i dim i deg i) degs
  in
  let where = String.concat " AND " where in
  let sql =
    sprintf
      {|SELECT nb_components, topology, COUNT() FROM variety%d as v%s WHERE %s
        GROUP BY topology|}
      nb pols where
  in
  db_log.log (fun k -> k "sql: %s" sql);
  let total = ref 0 in
  let res = ref [] in
  let cb row _ =
    res := row :: !res;
    total := !total + int_of_string row.(2);
  in
  Rc.check (exec_not_null (db ()) ~cb sql);
  let total_f = float !total in
  List.iter (fun row ->
      let nb = int_of_string row.(2) in
      let f = float nb /. total_f in
      let e = 2.326 *. sqrt (f *. (1.0 -. f) /. total_f) in
      printf "%s, %s => %s %5.2f%%±%3.2f%%\n"
        row.(0) row.(1) row.(2) (f *. 100.) (e *. 100.)) !res;
  printf "Total: %d\n%!" !total
