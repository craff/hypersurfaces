open Printing

type topology_one =
  | Any
  | Euler of int
  | Betti of int list

let alt_sum l =
  fst (List.fold_left (fun (acc,s) b -> (acc + s*b, -s)) (0,1) l)
let alt_sum_array l =
  fst (Array.fold_left (fun (acc,s) b -> (acc + s*b, -s)) (0,1) l)

let compare_one t1 t2 = match (t1, t2) with
  | Any, _ -> -1
  | _, Any -> 1
  | Euler n, Euler m -> compare n m
  | Euler n, Betti l -> compare n (alt_sum l)
  | Betti l, Euler m -> compare (alt_sum l) m
  | Betti l, Betti k ->
     begin
       match compare (alt_sum l) (alt_sum k) with
       | 0 -> compare l k
       | c -> c
     end

type topo_ask = Ask_Nbc | Ask_Euler | Ask_Betti

let min_demand topo =
  let fn acc (t,_) = match t with
    | Any -> acc
    | Euler _ -> max Ask_Euler acc
    | Betti _ -> max Ask_Betti acc
  in
  List.fold_left fn Ask_Nbc topo

let compare2 (t1,_) (t2,_) = compare_one t1 t2

(** topology are sorted by the compare order, and factorised, the positive
    integer being the number of components with that topology *)

type topology = (topology_one * int) list

let to_string t =
  let fn ch = function
    | Any -> fprintf ch "?"
    | Euler n -> fprintf ch "%d" n
    | Betti l -> fprintf ch "%a" print_int_list l
  in
  let gn (t,nb) =
    if nb = 0 then
      sprintf "0"
    else if nb = 1 then
      sprintf "%a" fn t
    else
      sprintf "%d*%a" nb fn t
  in
  "(" ^ String.concat "," (List.map gn t) ^ ")"

let print ch t = fprintf ch "%s" (to_string t)

let rm_trailing_zero l =
  let rec fn = function 0::l -> fn l | _ -> l in
  List.rev (fn (List.rev l))

let%parser rec betti =
    (n::INT)                => [n]
  ; (n::INT) ',' (l::betti) => n::l

let%parser topo_one =
    '?'                => Any
  ; (n::INT)           => Euler n
  ; '(' (l::betti) ')' => Betti (rm_trailing_zero l)

let%parser rec topo_mul =
    (n:: ~? [1] ((n::INT) '*' => n)) (t::topo_one) => (t, n)

let%parser rec topo_list =
    (t::topo_mul)                    => [t]
  ; (l::topo_list) "," (t::topo_mul) => t::l

let%parser parse =
  ()         => None
  ; (n::INT) => if n = 0 then Some[] else Some[(Any,n)]
  ; '(' ')'  => Some[]
  ; '(' (l:: topo_list) ')' => Some (List.sort compare2 l)

let blank = Pacomb.Regexp.blank_regexp "[ \t]*"

let of_string str =
  let open Pacomb in
  try
    match Grammar.parse_string parse blank str with
    | None -> failwith "Topology.of_string: blank string"
    | Some t -> t
  with e ->
    let msg = sprintf "Topology.of_string: %s" (Printexc.to_string e) in
    failwith msg

let _ = assert (Any < Euler 0 && Euler 0 < Betti [])

let better_one t1 t2 = match (t1,t2) with
  | (Any, _) -> false
  | (_  , Any) -> true
  | (Euler _, _) -> false
  | (_, Euler _) -> true
  | (Betti _, Betti _) -> false

let rec better ts1 ts2 =
  match (ts1, ts2) with
  | [], [] -> false
  | ((t1,n1)::ts1, (t2,n2)::ts2) ->
     if better_one t1 t2 then
       if n1 = n2 then better ts1 ts2
       else if n1 < n2 then better ts1 ((t2,n2-n1)::ts2)
       else better ((t1,n1-n2)::ts1) ts2
     else false
  | (_, _) -> false

let agree_one t1 t2 =
  match (t1, t2) with
  | (Any, _) | (_, Any) -> true
  | (Euler n, Euler m) -> n = m
  | (Euler n, Betti l) | (Betti l, Euler n) ->
     alt_sum l = n
  | (Betti l, Betti l') -> rm_trailing_zero l = rm_trailing_zero l'

let rec agree ts1 ts2 =
  match (ts1, ts2) with
  | [], [] -> true
  | ((t1,n1)::ts1, (t2,n2)::ts2) when agree_one t1 t2 ->
     if n1 = n2 then agree ts1 ts2
     else if n1 < n2 then agree ts1 ((t2,n2-n1)::ts2)
     else agree ((t1,n1-n2)::ts1) ts2
  | (_, _) -> false
