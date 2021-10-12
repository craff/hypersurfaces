(** {1: General code for fields implementation} *)

open Printing

(** Minimal signature for a field *)
module type SMin = sig
  type t
  val zero : t
  val one : t
  val inf : t
  val is_nan : t -> bool
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
  val to_int : t -> int
  val to_float : t -> float
  val of_float : float -> t
  val of_string : string -> t
  val to_string : t -> string
  val to_q : t -> Q.t
  val print : formatter -> t -> unit
  (** true is computation are exact, for rational for instance *)
  val exact : bool
  val cos : t -> t
  val sin : t -> t
  val ln  : t -> t
  val exp : t -> t
end

(** Complete field signature, with a few extra functions *)
module type S = sig
  include SMin

  val precision : int option (* number of bits *)
  val small : float -> t (* number using pourcentage of the precision *)
  (** power function, in O(ln n) *)
  val pow : t -> int -> t
  val powf : t -> t -> t
  val ball_integrals : (t array -> t) -> int -> int -> t
  val ball_integrals1 : t array -> (t array -> t array) -> int -> int -> t array
  val ball_integrals2 : t array array -> (t array -> t array array) -> int -> int -> t array array
  val rk4 : ?debug:(t -> t -> unit) -> (t -> t -> t) -> t -> t -> t -> int -> t
  val rk4_1 : ?debug:(t -> t array -> unit) -> (t -> t array -> t array) -> t -> t -> t array -> int -> t array

  type stop_cond =
    { precision : t      (** |x - y| <= value *)
    ; max_steps : int    (** maximum number of steps *)
    }

  val default_stop_cond : stop_cond
  (** = { precision = zero
        ; max_steps = max_int }
  By default, dighotomie stops when value become equal, which always
  happens in precision steps. Will loop for rational.
  *)

  val solve_trinome : t -> t -> t -> t * t
  (** solve_trinome a b c: gives the two solutions of ax^2 + bx + c = 0.
      if no solution exists, raises Not_found. It one solution exists,
      it is duplicated *)

  (** [digho ?stop_cond f x y] finds an approximation of
      a root of [f] between [x] and [y].*)
  val digho : ?stop_cond:stop_cond -> (t -> t) -> t -> t -> t

  (** [trigho ?stop_cond f x y] finds an approximation of
      a local minimum of [f] between [x] and [y].
      we use the "golden ratio" version that ensures a minimum
      number of computation of [f] te reach a given precision
   *)
  val tricho : ?safe:bool -> ?stop_cond:stop_cond -> (t -> t) -> t -> t -> t
  val secant : ?safe:bool -> ?stop_cond:stop_cond -> (t -> t) -> t -> t -> t

  (** least float such that [one + epsilon != one] *)
  val epsilon : t
  (** square of epsilon *)
  val epsilon2 : t
end
