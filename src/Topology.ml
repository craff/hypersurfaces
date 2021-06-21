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
  let rec fn acc (t,_) = match t with
    | Any -> acc
    | Euler _ -> max Ask_Euler acc
    | Betti _ -> max Ask_Betti acc
  in
  List.fold_left fn Ask_Nbc topo

let compare2 (t1,n1) (t2,n2) = compare_one t1 t2

(** topology are sorted by the compare order, and factorised, the positive
    integer being the number of components with that topology *)

type topology = (topology_one * int) list

let to_string t =
  let fn ch = function
    | Any -> fprintf ch "?"
    | Euler n -> fprintf ch "%d" n
    | Betti l -> fprintf ch "%a" print_int_list l
  in
  let gn i (t,nb) =
    if nb = 1 then
      sprintf "%a" fn t
    else
      sprintf "%d*%a" nb fn t
  in
  String.concat "," (List.mapi gn t)

let print ch t = fprintf ch "%s" (to_string t)

let%parser rec betti =
    (n::INT)                => [n]
  ; (n::INT) ',' (l::betti) => n::l

let%parser topo_one =
    (n::INT)           => Euler n
  ; '(' (l::betti) ')' => Betti l

let%parser rec topo_mul =
    (n:: ~? [1] ((n::INT) '*' => n)) (t::topo_one) => (t, n)

let%parser rec topo_list =
    (t::topo_mul)                    => [t]
  ; (l::topo_list) "," (t::topo_mul) => t::l

let%parser parse =
    ()       => None
  ; (n::INT) => Some[(Any,n)]
  ; '(' ')'  => Some[]
  ; '(' (l:: topo_list) ')' => Some (List.sort compare2 l)

let _ = assert (Any < Euler 0 && Euler 0 < Betti [])

let agree_one t1 t2 =
  match (t1, t2) with
  | (Any, _) | (_, Any) -> true
  | (Euler n, Euler m) -> n = m
  | (Euler n, Betti l) | (Betti l, Euler n) ->
     alt_sum l = n
  | (Betti l, Betti l') -> l = l'

let rec agree ts1 ts2 =
  match (ts1, ts2) with
  | [], [] -> true
  | ((t1,n1)::ts1, (t2,n2)::ts2) when agree_one t1 t2 ->
     if n1 = n2 then agree ts1 ts2
     else if n1 < n2 then agree ts1 ((t2,n2-n1)::ts2)
     else agree ((t1,n1-n2)::ts1) ts2
  | (_, _) -> false
