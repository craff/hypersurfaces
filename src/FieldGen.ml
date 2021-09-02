(** {1: General code for fields implementation} *)

open Printing

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
  val to_int : t -> int
  val to_float : t -> float
  val of_float : float -> t
  val of_string : string -> t
  val to_string : t -> string
  val print : formatter -> t -> unit
  (** true is computation are exact, for rational for instance *)
  val exact : bool
  val cos : t -> t
  val ln  : t -> t
  val exp : t -> t
end

(** Complete field signature, with a few extra functions *)
module type S = sig
  include SMin
  (** power function, in O(ln n) *)
  val pow : t -> int -> t
  val powf : t -> t -> t

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

  let powf x y = exp (y *. ln x)

  type stop_cond =
    { precision : t      (** |x - y| <= value *)
    ; max_steps : int    (** maximum number of steps *)
    }

  let solve_trinome a b c =
    if a =. zero then (-.c /. b, -.c /. b) else
      begin
        let delta = b *. b -. of_int 4 *. a *. c in
        if delta <. zero then raise Not_found;
        if b >. zero then
          ((-. b -. sqrt delta) /. (of_int 2 *. a),
           (of_int 2 *. c) /. (-.b -. sqrt delta))
        else
          ((-. b +. sqrt delta) /. (of_int 2 *. a),
           (of_int 2 *. c) /. (-. b +. sqrt delta))
      end


  let default_stop_cond = { precision = zero
                          ; max_steps = max_int }

  let digho ?(stop_cond=default_stop_cond) f x y =
    let fx = f x and fy = f y in
    let steps = ref 0 in
    let h = one /. of_int 2 in
    let rec fn x fx y fy =
      incr steps;
      let z = (x +. y) *. h in
      if abs (y -. x) <=. stop_cond.precision
         || !steps > stop_cond.max_steps then z
      else
        let fz = f z in
        match cmp fz zero with
        | 0 -> z
        | c when c < 0 -> fn z fz y fy
        | _ -> fn x fx z fz
    in
    match cmp fx zero, cmp fy zero with
    | 0, _ -> x
    | _, 0 -> y
    | c1, c2 when c1 < 0 && c2 > 0 -> fn x fx y fy
    | c1, c2 when c1 > 0 && c2 < 0 -> fn y fy x fx
    | _ -> invalid_arg "digho same sign"

  let g = (sqrt (of_int 5) -. one) /. of_int 2

  let secant ?(safe=true) ?(stop_cond=default_stop_cond) f beta0 beta2 =
    let beta0, beta2 =
      if beta2 >. beta0 then (beta0, beta2) else (beta2, beta0)
    in
    let steps = ref 0 in
    let rec fn beta0 f0 beta1 f1 beta2 f2 =
(*      printf "%d: %a %a %a %a %a %a\n%!" !steps print beta0 print f0
        print beta1 print f1
        print beta2 print f2;*)
      if !steps >= stop_cond.max_steps
         || abs ((f0 -. f1) /. f0) <=. stop_cond.precision
         || abs ((f2 -. f1) /. f0) <=. stop_cond.precision
      then beta1 else
        let d1 = (f1 -. f0) /. (beta1 -. beta0) in
        let d2 = (f2 -. f1) /. (beta2 -. beta1) in
        let x = (d1 /. (d1 -. d2)) *. (beta2 -. beta0) +. beta0 in
        let (x,f) =
          if x >. beta0 && x <. beta2 && abs (x -. beta1) >. of_float 1e-4 *. (beta2 -. beta0) then (x, f x)
          else
            let x =
              if beta2 -. beta1 > beta1 -. beta0 then
                (beta1 +. beta2) /. of_int 2
              else
                (beta0 +. beta1) /. of_int 2
            in
            (x,f x)
        in
        incr steps;
        if x <. beta1 then
          if f <. f1 then
            fn beta0 f0 x f beta1 f1
          else
            fn x f beta1 f1 beta2 f2
        else if f <. f1 then
          fn beta1 f1 x f beta2 f2
        else
          fn beta0 f0 beta1 f1 x f
    in
    let beta1 = (beta0 +. beta2) /. of_int 2 in
    let f0 = f beta0 in
    let f1 = f beta1 in
    let f2 = f beta2 in
    let beta = fn beta0 f0 beta1 f1 beta2 f2 in
    if safe then beta else
      begin
        let f = f beta in
        if f <. f0 && f <. f2 then beta
        else if f0 <. f2 then beta0 else beta1
      end

  let tricho ?(safe=true) ?(stop_cond=default_stop_cond) f beta0 beta3 =
    let steps = ref 0 in
    let rec fn beta0 beta2 f2 beta3 =
      if !steps >= stop_cond.max_steps
         || abs (beta3 -. beta0) <=. stop_cond.precision
      then beta2 else
        begin
          incr steps;
          let beta1 = beta3 -. g *. (beta3 -. beta0) in
          let f1 = f beta1 in
          if f1 <. f2 then fn beta0 beta1 f1 beta2
          else gn beta1 beta2 f2 beta3
        end
    and gn beta0 beta1 f1 beta3 =
      if !steps >= stop_cond.max_steps
         || abs (beta3 -. beta0) <=. stop_cond.precision
      then beta1 else
        begin
          incr steps;
          let beta2 = beta0 +. g *. (beta3 -. beta0) in
          let f2 = f beta2 in
          if f1 <. f2 then fn beta0 beta1 f1 beta2
          else gn beta1 beta2 f2 beta3
        end
    in
    let beta1 = beta3 -. g *. (beta3 -. beta0) in
    let f1 = f beta1 in
    let beta2 = beta0 +. g *. (beta3 -. beta0) in
    let f2 = f beta2 in
    let beta =
      if f1 <. f2 then fn beta0 beta1 f1 beta2
      else if f2 <. f1 then gn beta1 beta2 f2 beta3
      else beta2
    in
    if safe then beta else
      begin
        let f0 = f beta0 in
        let f3 = f beta3 in
        let f = f beta in
        if f <. f0 && f <. f3 then beta
        else if f0 <. f3 then beta0 else beta1
      end

  (* precision *)
  let epsilon = if exact then zero else
                  let rec fn nb x =
                    if (one +. x =. one) then pow (one /. of_int 2) nb
                    else fn (nb + 1) (x /. of_int 2)
                  in
                  let r = fn 0 one in
                  (*Printf.printf "%a\n%!" print r;*)
                  r

  let epsilon2 = epsilon *. epsilon
end
