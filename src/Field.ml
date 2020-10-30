  (** Minimal signature for a field *)
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
  val of_float : float -> t
  val of_string : string -> t
  val print : out_channel -> t -> unit
  val exact : bool
end

(** Field signature *)
module type S = sig
  include SMin
  val pow : t -> int -> t
  val digho : (t -> t) -> t -> t -> t -> t -> int -> t
  val epsilon : t
  val epsilon2 : t
end

(** Functor building a field from the minimum signature *)
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

    (* precision *)
    let epsilon = if exact then zero else
      let rec fn nb x =
        if (one +. x =. one) then pow (one /. of_int 2) nb
        else fn (nb + 1) (x /. of_int 2)
      in
      let r = fn 0 one in
      Printf.printf "%a\n%!" print r;
      r

    let epsilon2 = epsilon *. epsilon

end

(** Float field *)
module Float =
  Make(struct
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
    let of_float x = x
    let of_string = float_of_string
    let print ch = Printf.fprintf ch "%e"
    let exact = false
  end)

(** Gmp multiprecision *)
module Gmp_R(Prec: sig val prec: int end) : S =
  Make(struct
      open Mpfrf
      let mode = Mpfr.Near
      let _ = Mpfr.set_default_prec Prec.prec
      type nonrec t = t
      let zero = of_int 0 mode
      let one = of_int 1 mode
      let ( +. ) x y = add x y mode
      let ( *. ) x y = mul x y mode
      let ( -. ) x y = sub x y mode
      let ( /. ) x y = div x y mode
      let ( ~-.) x = neg x mode
      let sqrt x = sqrt x mode
      let inf = one /. zero
      let cmp = Mpfr.cmp
      let ( =. ) x y = cmp x y = 0
      let ( <>. ) x y = cmp x y <> 0
      let ( <. ) x y = cmp x y < 0
      let ( >. ) x y = cmp x y > 0
      let ( <=. ) x y = cmp x y <= 0
      let ( >=. ) x y = cmp x y >= 0
      let abs x = abs x mode
      let of_int x = of_int x mode
      let to_float x = to_float x
      let of_float x = of_float x mode
      let of_string x = of_string x mode
      let print ch x = output_string ch (to_string x)
      let exact = false
    end)

(** Zarith rational, not usable yet *)
module Q:S =
  Make(struct
    type t = Q.t
    open Q
    let zero = zero
    let one = one
    let inf = inf
    let ( +. ) = add
    let ( *. ) = mul
    let ( -. ) = sub
    let ( /. ) = div
    let ( ~-.) = neg
    let ( =. ) = ( = )
    let ( <>. ) = ( <> )
    let ( <. ) = ( < )
    let ( >. ) = ( > )
    let ( <=. ) = ( <= )
    let ( >=. ) = ( >= )
    let step_sqrt = 5
    let sqrt x =
      let y = ref x in
      let two = one +. one in
      for i = 1 to step_sqrt do
        y := (x /. !y +. !y) /. two
      done;
      !y
    let cmp = compare
    let abs = abs
    let of_int = of_int
    let to_float = to_float
    let of_float = of_float
    let of_string = of_string
    let print ch x = Printf.fprintf ch "%s" (to_string x)
    let exact = true
    let _ = print stdout (sqrt (of_int 2)); Printf.printf " %.15e %.15e \n%!" (to_float (sqrt (of_int 2))) (Stdlib.sqrt 2.0)
  end)
