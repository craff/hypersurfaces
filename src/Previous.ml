type 'a previous =
  { data : 'a option array
  ; mutable current : int }

let create : type a. int -> a previous = fun n ->
  { data = Array.make n None; current = 0 }

let add : type a. a -> a previous -> unit = fun x r ->
  r.data.(r.current) <- Some x;
  r.current <- (r.current + 1) mod Array.length r.data

let get : type a. a previous -> a = fun r ->
  match r.data.(r.current) with
  | Some x -> x
  | None -> raise Not_found
