
type ('a,'b) sum = InL of 'a | InR of 'b

let find_i f l =
  let rec fn i l =
    match l with
    | [] -> None
    | (x::l) -> if f x then Some i else fn (i+1) l
  in
  fn 0 l

let hashtbl_map fn tbl =
  let res = Hashtbl.create 1024 in
  Hashtbl.iter (fun key v -> Hashtbl.add res key (fn v)) tbl;
  res
