open Printing

module type SPlus = sig
  include FieldGen.S

  module V : Vector.V with type t = t
  module B : Polynomial.B with type t = t and
                               type v = V.v and
                               type m = V.m
end

(** Float field *)
module FloatMin =
  struct
    type t = float
    let zero = 0.
    let one = 1.
    let inf = infinity
    let ( +. ) = ( +. ) [@@inlined]
    let ( *. ) = ( *. ) [@@inlined]
    let ( -. ) = ( -. ) [@@inlined]
    let ( /. ) = ( /. ) [@@inlined]
    let ( ~-.) = ( ~-.) [@@inlined]
    let ( =. ) : float -> float -> bool = ( = ) [@@inlined]
    let ( <>. ): float -> float -> bool = ( <> )[@@inlined]
    let ( <. ) : float -> float -> bool = ( < ) [@@inlined]
    let ( >. ) : float -> float -> bool = ( > ) [@@inlined]
    let ( <=. ): float -> float -> bool = ( <= )[@@inlined]
    let ( >=. ): float -> float -> bool = ( >= )[@@inlined]
    let sqrt = sqrt
    let cmp : float -> float -> int = Stdlib.compare
    let abs = abs_float
    let of_int = float
    let to_int = int_of_float
    let to_float x = x [@@inlined]
    let of_float x = x [@@inlined]
    let of_string = float_of_string
    let to_string = Format.sprintf "%.13H"
    let to_q = Q.of_float
    let print ch = fprintf ch "%.18e"
    let exact = false
    let cos = cos
    let sin = sin
    let ln = log
    let exp = exp
  end

module Float = struct
  module F = FFieldMake.Make [@inlined] (FloatMin)
  include F
  module V = FVector.Make [@inlined] (F)
  module B = FPolynomial.Make (F) [@inlined] (V)
end

module GmpMin = struct
  open Mpfrf
  let mode = Mpfr.Near

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
  let to_int x = int_of_float (to_float x)
  let to_float x = to_float x
  let of_float x = of_float x mode
  let of_string x = of_string x mode
  let to_string x = to_string x
  let to_q x =
    let r = Mpfrf.to_mpqf x in
    let r = Mpqf.to_string r in
    Q.of_string r
  let print ch x = fprintf ch "%s" (to_string x)
  let exact = false
  let cos x =
    let r = Mpfr.init () in
    ignore (Mpfr.cos r (_mpfr x) mode);
    _mpfrf r
  let sin x =
    let r = Mpfr.init () in
    ignore (Mpfr.sin r (_mpfr x) mode);
    _mpfrf r
  let ln x =
    let r = Mpfr.init () in
    ignore (Mpfr.log r (_mpfr x) mode);
    _mpfrf r
  let exp x =
    let r = Mpfr.init () in
    ignore (Mpfr.exp r (_mpfr x) mode);
    _mpfrf r
end

module Gmp = struct
  let set_prec = Mpfr.set_default_prec
  let _ = set_prec 100

  module F = FieldMake.Make (GmpMin)
  include F
  module V = Vector.Make (F)
  module B = Polynomial.Make (F) (V)
end

(** Zarith rational, not usable yet *)
module QMin =
  struct
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
      for _ = 1 to step_sqrt do
        y := (x /. !y +. !y) /. two
      done;
      !y
    let cmp = compare
    let abs = abs
    let of_int = of_int
    let to_int = to_int
    let to_float = to_float
    let of_float = of_float
    let of_string = of_string
    let to_string = to_string
    let to_q x = x
    let print ch x = fprintf ch "%s" (to_string x)
    let exact = true
    let cos _ = failwith "cos not available"
    let sin _ = failwith "sin not available"
    let ln _  = failwith "ln not available"
    let exp _  = failwith "exp not available"
  end

module Q = struct
  module F = FieldMake.Make (QMin)
  include F
  module V = Vector.Make (F)
  module B = Polynomial.Make (F) (V)

end
