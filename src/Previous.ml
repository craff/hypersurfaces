type 'a previous =
  { data : 'a option array
  ; mutable current : int }

let create : type a. int -> a previous = fun n ->
  { data = Array.make n None; current = 0 }

let add : type a. a -> a previous -> unit = fun x r ->
  r.data.(r.current) <- Some x;
  r.current <- (r.current + 1) mod Array.length r.data

let get : type a. ?pos:int -> a previous -> a = fun ?(pos= (-1)) r ->
  let i = r.current - 1 - pos in
  let i = i mod (Array.length r.data) in
  let i = if i < 0 then i + Array.length r.data else i in
  match r.data.(i) with
  | Some x -> x
  | None -> raise Not_found

let max_size : type a. a previous -> int = fun q -> Array.length q.data

let size : type a. a previous -> int = fun q ->
  let len = Array.length q.data in
  if q.data.(0) = None then 0
  else if q.data.(len-1) <> None then len
  else
    (* loop invariant: 0 <= a < b < len
                       q.data.(a) <> None,
                       q.data.(b) = None *)
    let rec fn a b =
      if a = b - 1 then b
      else
        let c = (a + b) / 2 in
        if q.data.(c) = None then
          fn a c
        else fn c b
    in
    fn 0 (len - 1)
