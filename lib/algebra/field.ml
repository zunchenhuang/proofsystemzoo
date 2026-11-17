(* Coefficient fields.

   One signature, two implementations: GF(p) for a prime p < 2^30, whose
   elements are a private [int] in [0, p) (a product of two elements fits in
   a 63-bit integer, so arithmetic never allocates), and ℚ on Zarith. The
   algebraic systems are functors over [S]: the same Nullstellensatz or
   Polynomial Calculus code runs over any field, and the type checker keeps
   elements of different fields apart. *)

module type S = sig
  type t

  val name : string
  val characteristic : int (* 0 for ℚ *)
  val zero : t
  val one : t
  val of_int : int -> t
  val of_z : Z.t -> t
  val add : t -> t -> t
  val sub : t -> t -> t
  val neg : t -> t
  val mul : t -> t -> t
  val inv : t -> t (* raises Division_by_zero on zero *)
  val div : t -> t -> t
  val is_zero : t -> bool
  val is_one : t -> bool
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val to_string : t -> string
  val codec : t Json.codec
end

module type PRIME = sig
  val p : int
end

module Gf (P : PRIME) : sig
  include S with type t = private int

  val to_int : t -> int
end = struct
  let p =
    if Num.is_prime P.p && P.p < 1 lsl 30 then P.p
    else invalid_arg (Printf.sprintf "GF(%d): not a prime below 2^30" P.p)

  type t = int

  let name = Printf.sprintf "GF(%d)" p
  let characteristic = p
  let zero = 0
  let one = 1

  let of_int a =
    let r = a mod p in
    if r < 0 then r + p else r

  let of_z z = Z.to_int (Z.erem z (Z.of_int p))

  let add a b =
    let s = a + b in
    if s >= p then s - p else s

  let sub a b =
    let s = a - b in
    if s < 0 then s + p else s

  let neg a = if a = 0 then 0 else p - a
  let mul a b = a * b mod p

  (* extended Euclid: r_i ≡ s_i·a (mod p) throughout *)
  let inv a =
    if a = 0 then raise Division_by_zero;
    let rec go r0 r1 s0 s1 = if r1 = 0 then s0 else go r1 (r0 - (r0 / r1 * r1)) s1 (s0 - (r0 / r1 * s1)) in
    of_int (go a p 1 0)

  let div a b = mul a (inv b)
  let is_zero a = a = 0
  let is_one a = a = 1
  let equal = Int.equal
  let compare = Int.compare
  let to_int a = a
  let to_string = string_of_int
  let codec = Json.codec (fun a -> `Int a) (fun j -> Result.map of_int (Json.D.int j))
end

module Rational : S with type t = Q.t = struct
  type t = Q.t

  let name = "Q"
  let characteristic = 0
  let zero = Q.zero
  let one = Q.one
  let of_int = Q.of_int
  let of_z = Q.of_bigint
  let add = Q.add
  let sub = Q.sub
  let neg = Q.neg
  let mul = Q.mul

  let inv a =
    if Q.sign a = 0 then raise Division_by_zero;
    Q.inv a

  let div a b = mul a (inv b)
  let is_zero a = Q.sign a = 0
  let is_one a = Q.equal a Q.one
  let equal = Q.equal
  let compare = Q.compare
  let to_string = Q.to_string
  let codec = Json.q
end
