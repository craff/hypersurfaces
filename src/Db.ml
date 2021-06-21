open Sqlite3
open Format

let create_polynomial = "
  CREATE TABLE IF NOT EXISTS polynomial (
    value TEXT PRIMARY KEY,
    degree INTEGER,
    dimension INTEGER,
    random INT(1))"

let rec pkey n = match n with
  | _ when n <= 0 -> assert false
  | 1             -> "p0 INTEGER"
  | n             -> sprintf "%s, p%d INTEGER" (pkey (n-1)) (n-1)

let create_variety n = sprintf
  "CREATE TABLE IF NOT EXISTS variety%d (
    %s,
    nb_components INTEGER,
    euler_characteristic TEXT)" n (pkey n)
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
       eprintf "data base %s created\n%!" name;
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
  let cb row headers =
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

let insert_variety to_str ps dim nbc euler =
  try
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
        "SELECT nb_components, euler_characteristic FROM variety%d WHERE %s"
        nb_pol pid_sel
    in
    let res = ref None in
    let cb row headers =
      assert (Array.length row = 2);
      res := Some (int_of_string row.(0), row.(1))
    in
    Rc.check (exec_not_null (db ()) ~cb sql);
    match !res with
    | Some (nbc', euler') ->
       if nbc' <> nbc || euler <> euler' then
         begin
           eprintf "BAD VARIETY IN DATABASE";
           exit 1
         end
    | None ->
       let pid_ins = String.concat "," (List.map Int64.to_string pid) in
       let sql =
         sprintf "INSERT INTO variety%d VALUES (%s,%d,'%s')" nb_pol pid_ins nbc euler
       in
       Rc.check (exec (db ()) sql);
  with
    SqliteError s ->
     eprintf "can not insert variety: %s\n%!" s;
     exit 1

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
      "SELECT nb_components, euler_characteristic FROM variety%d as v%s WHERE %s"
      nb pols where
  in
  printf "sql: %s\n%!" sql;
  let tbl = Hashtbl.create 1001 in
  let total = ref 0 in
  let cb row headers =
    let nb = try Hashtbl.find tbl row with Not_found -> 0 in
    incr total;
    Hashtbl.replace tbl row (nb+1)
  in
  Rc.check (exec_not_null (db ()) ~cb sql);
  let total_f = float !total in
  Hashtbl.iter (fun row nb ->
      let f = float nb /. total_f in
      let e = 2.326 *. sqrt (f *. (1.0 -. f) /. total_f) in
      printf "%s, %s => %d %5.2f%%±%3.2f%%\n"
        row.(0) row.(1) nb (f *. 100.) (e *. 100.)) tbl;
  printf "Total: %d\n%!" !total
