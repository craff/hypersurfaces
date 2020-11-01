
let debug_list = ref []

let new_debug ?(ch=stderr) name letter =
  let pr = ref false in
  debug_list := (letter, pr) :: !debug_list;
  let fn fmt =
    let pr = if !pr then Printf.fprintf else Printf.ifprintf in
    pr ch ("%s: " ^^ fmt ^^ "\n%!") name
  in
  fn

let set_debugs debugs =
  List.iter (fun (l,pr) -> pr := false) !debug_list;
  String.iter (fun c ->
      try let pr = List.assoc c !debug_list in pr := true
      with Not_found ->
        let msg = Printf.sprintf "%C: no debug" c in
        failwith msg) debugs
