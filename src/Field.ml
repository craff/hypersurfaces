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
    let is_nan = Float.is_nan
    let ( +. ) = ( +. )
    let ( *. ) = ( *. )
    let ( -. ) = ( -. )
    let ( /. ) = ( /. )
    let ( ~-.) = ( ~-.)
    let ( =. ) : float -> float -> bool = ( = )
    let ( <>. ): float -> float -> bool = ( <> )
    let ( <. ) : float -> float -> bool = ( < )
    let ( >. ) : float -> float -> bool = ( > )
    let ( <=. ): float -> float -> bool = ( <= )
    let ( >=. ): float -> float -> bool = ( >= )
    let sqrt = sqrt
    let cmp : float -> float -> int = Stdlib.compare
    let abs = abs_float
    let of_int = float
    let to_int = int_of_float
    let to_float x = x [@@inline always]
    let of_float x = x [@@inline always]
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
  open Mlmpfr
  let _ = set_default_rounding_mode To_Nearest

  type nonrec t = mpfr_float
  let zero = make_from_int 0
  let one = make_from_int 1
  let is_nan = nan_p
  let ( +. ) x y = add x y
  let ( *. ) x y = mul x y
  let ( -. ) x y = sub x y
  let ( /. ) x y = div x y
  let ( ~-.) x = neg x
  let inf = one /. zero
  let sqrt x = sqrt x
  let cmp = cmp
  let ( =. ) x y = cmp x y = 0
  let ( <>. ) x y = cmp x y <> 0
  let ( <. ) x y = cmp x y < 0
  let ( >. ) x y = cmp x y > 0
  let ( <=. ) x y = cmp x y <= 0
  let ( >=. ) x y = cmp x y >= 0
  let abs x = abs x
  let of_int x = make_from_int x
  let to_int x = get_int x
  let to_float x = get_float x
  let of_float x = make_from_float x
  let of_string x = make_from_str x
  let get_str x = let (f,e) = get_str x in f ^"E" ^ e (* TODO: check meaning of e *)
  let to_string x = get_str x
  let to_q x =
    let r = get_str x in
    Q.of_string r
  let print ch x = fprintf ch "%s" (get_str x)
  let exact = false
  let cos x = cos x
  let sin x = sin x
  let ln x = log x
  let exp x = exp x
end

module Gmp = struct
  let set_prec = Mlmpfr.set_default_prec
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
    let is_nan x = not (is_real x)
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
