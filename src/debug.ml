
let debug_list = ref []

(** a debug channel provide a printing function, that will
    print to stderr with the name of the debug channel as prefix.
    It also prints a newline and flushes output automatically.

    It also provide a test function, usefull if some debug code
    requires computation that could have a significant cost. A
    test can be used to avoid the computation when the default
    channel is not active. *)
type debug = { log : 'a.('a, out_channel, unit) format -> 'a
             ; tst : unit -> bool }

(** create a new debug channel, with its name and a given letter.
    This gives 26 possible debug channel if using only lowercase letter.
    much more is using more characteres. *)
let new_debug ?(ch=stderr) name letter =
  let pr = ref false in
  if List.mem_assoc letter !debug_list then
    begin
      let msg = Printf.sprintf "%C: debug exists" letter in
      failwith msg
    end;
  debug_list := (letter, pr) :: !debug_list;
  let tst () = !pr in
  let log fmt =
    let pr = if tst () then Printf.fprintf else Printf.ifprintf in
    pr ch ("%s: " ^^ fmt ^^ "\n%!") name
  in
  {tst; log}

(** set which debug channels are active, using the characters in the string
    debug *)
let set_debugs debugs =
  List.iter (fun (_,pr) -> pr := false) !debug_list;
  String.iter (fun c ->
      try let pr = List.assoc c !debug_list in pr := true
      with Not_found ->
        let msg = Printf.sprintf "%C: no debug" c in
        failwith msg) debugs

(** check if at least one debug channel is active *)
let has_debug () = List.exists (fun (_,pr) -> !pr) !debug_list

(** print to stderr and assert false *)
let assert_log fmt =
  Printf.kfprintf (fun _ -> assert false) stderr fmt

(** if cond is true, print to stderr and assert false *)
let assert_cond cond fmt =
  if cond then
    Printf.kfprintf (fun _ -> assert false) stderr fmt
