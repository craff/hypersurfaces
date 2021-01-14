
type 'a uf_cell = Link of 'a uf | Root of 'a

and 'a uf = 'a uf_cell ref

let new_uf x = ref (Root x)

let rec find l = match !l with
  | Root _ -> l
  | Link r -> let r' = find r in
              if r' != r then l := Link r';
              r'

let find_data l =
  match !(find l) with
  | Root x -> x
  | _      -> assert false

let union f s1 s2 =
  let s1 = find s1 in
  let s2 = find s2 in
  if s1 == s2 then () else
  match (!s1, !s2) with
  | Root r1, Root r2 -> s1 := Link s2; s2 := Root (f r1 r2)
  | _                -> assert false
