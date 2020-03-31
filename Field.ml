module type S = sig
  type t
  val zero : t
  val one : t
  val ( +. ) : t -> t -> t
  val ( *. ) : t -> t -> t
  val ( -. ) : t -> t -> t
  val ( /. ) : t -> t -> t
  val ( ~-. ) : t -> t
  val pow : t -> int -> t
  val cmp : t -> t -> int
  val abs : t -> t
  val of_int : int -> t
  val to_float : t -> float
  val print : out_channel -> t -> unit
end

(** Float field *)
module Float:S with type t = float = struct
  type t = float
  let zero = 0.
  let one = 1.
  let ( +. ) = ( +. )
  let ( *. ) = ( *. )
  let ( -. ) = ( -. )
  let ( /. ) = ( /. )
  let ( ~-.) = ( ~-.)
  let pow x n =
    let (x,n) = if n < 0 then (one /. x, -n) else (x,n) in
    let rec fn n =
      if n <= 0 then one
      else if n = 1 then x
      else
        let q = fn (n lsr 1) in
        let q2 = q *. q in
        if n land 0x1 = 0 then q2 else q2 *. x
    in
    fn n
  let cmp = compare
  let abs = abs_float
  let of_int = float
  let to_float x = x
  let print ch = Printf.fprintf ch "%e"
end

(** Rational field from Zarith *)
module Q:S with type t = Q.t = struct
  open Q
  type t = Q.t
  let zero = zero
  let one = one
  let ( +. ) = ( + )
  let ( *. ) = ( * )
  let ( -. ) = ( - )
  let ( /. ) = ( / )
  let ( ~-.) = ( ~-)
  let pow (x:t) (n:int) =
    let (x,n) = if Stdlib.(n < 0) then (one /. x, Stdlib.(-n)) else (x,n) in
    let rec fn n =
      if Stdlib.(n <= 0) then one
      else if Stdlib.(n = 1) then x
      else
        let q = fn (n lsr 1) in
        let q2 = q *. q in
        if Stdlib.(n land 0x1 = 0) then q2 else q2 *. x
    in
    fn n
  let cmp = Q.compare
  let abs = Q.abs
  let of_int x = of_ints x 1
  let to_float x = Stdlib.(Z.to_float x.num /. Z.to_float x.den)
  let print = output
end
