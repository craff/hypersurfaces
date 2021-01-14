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

let zih_log = Debug.new_debug "hull" 'h'
let zih_tst = zih_log.tst
let zih_log fmt = zih_log.log fmt

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

  let digho f x fx y fy nb =
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
                  (*Printf.printf "%a\n%!" print r;*)
                  r

  let epsilon2 = epsilon *. epsilon
end
