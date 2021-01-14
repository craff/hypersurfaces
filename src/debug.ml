
let debug_list = ref []

type debug = { log : 'a.('a, out_channel, unit) format -> 'a
             ; tst : unit -> bool }

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

let set_debugs debugs =
  List.iter (fun (_,pr) -> pr := false) !debug_list;
  String.iter (fun c ->
      try let pr = List.assoc c !debug_list in pr := true
      with Not_found ->
        let msg = Printf.sprintf "%C: no debug" c in
        failwith msg) debugs

let has_debug () = List.exists (fun (_,pr) -> !pr) !debug_list

let assert_log fmt =
  Printf.kfprintf (fun _ -> assert false) stderr fmt

let assert_cond cond fmt =
  if cond then
    Printf.kfprintf (fun _ -> assert false) stderr fmt
