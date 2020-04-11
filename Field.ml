module type SMin = sig
  type t
  val zero : t
  val one : t
  val inf : t
  val ( +. ) : t -> t -> t
  val ( *. ) : t -> t -> t
  val ( -. ) : t -> t -> t
  val ( /. ) : t -> t -> t
  val ( ~-. ) : t -> t
  val cmp : t -> t -> int
  val (=.) : t -> t -> bool
  val (<>.) : t -> t -> bool
  val (<.) : t -> t -> bool
  val (>.) : t -> t -> bool
  val (<=.) : t -> t -> bool
  val (>=.) : t -> t -> bool
  val abs : t -> t
  val sqrt : t -> t
  val of_int : int -> t
  val to_float : t -> float
  val print : out_channel -> t -> unit
end

module type S = sig
  include SMin
  val pow : t -> int -> t
  val digho : (t -> t) -> t -> t -> t -> t -> int -> t
  val epsilon : t
end

module Make(R:SMin) = struct
    include R

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

    let rec digho f x fx y fy nb =
      let h = one /. of_int 2 in
      let rec fn x fx y fy nb =
        Printf.printf "*%!";
        let z = (x +. y) *. h in
        if nb = 0 then z else
          let fz = f z in
          match cmp fz zero with
          | 0 -> z
          | c when c < 0 -> fn z fz y fy (nb - 1)
          | _ -> fn x fx z fz (nb -1)
      in
      match cmp fx zero, cmp fy zero with
      | 0, _ -> x
      | _, 0 -> y
      | c1, c2 when c1 < 0 && c2 > 0 -> fn x fx y fy nb
      | c1, c2 when c1 > 0 && c2 < 0 -> fn y fy x fx nb
      | _ -> invalid_arg "digho same sign"

    let epsilon =
      let rec fn nb x =
        if (one +. x =. one) then pow (one /. of_int 2) ((9 * nb) / 10)
        else fn (nb + 1) (x /. of_int 2)
      in
      let r = fn 0 one in
      Printf.printf "%a\n%!" print r;
      r
end

(** Float field *)
module Float:S = Make(struct
  type t = float
  let zero = 0.
  let one = 1.
  let inf = infinity
  let ( +. ) = ( +. )
  let ( *. ) = ( *. )
  let ( -. ) = ( -. )
  let ( /. ) = ( /. )
  let ( ~-.) = ( ~-.)
  let ( =. ) = ( = )
  let ( <>. ) = ( <> )
  let ( <. ) = ( < )
  let ( >. ) = ( > )
  let ( <=. ) = ( <= )
  let ( >=. ) = ( >= )
  let sqrt = sqrt
  let cmp = compare
  let abs = abs_float
  let of_int = float
  let to_float x = x
  let print ch = Printf.fprintf ch "%e"
  let exact = false
end)

module Gmp_R(Prec: sig val prec: int end) : S =
  Make(struct
      open Mpfr.FR(Prec)
      let mode = `N
      type nonrec t = t
      let zero = zero
      let one = one
      let ( +. ) = add ~mode
      let ( *. ) = mul ~mode
      let ( -. ) = sub ~mode
      let ( /. ) = div ~mode
      let ( ~-.) = neg ~mode
      let sqrt = sqrt ~mode
      let inf = one /. zero
      let cmp = compare
      let ( =. ) x y = cmp x y = 0
      let ( <>. ) x y = cmp x y <> 0
      let ( <. ) x y = cmp x y < 0
      let ( >. ) x y = cmp x y > 0
      let ( <=. ) x y = cmp x y <= 0
      let ( >=. ) x y = cmp x y >= 0
      let abs = abs ~mode
      let of_int = of_int ~mode
      let to_float = to_float ~mode
      let print ch x = output_string ch (to_string ~mode x)
      let exact = false
    end)
