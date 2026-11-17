(* Multilinear monomials: sets of variables (x² = x on 0/1 points).

   [Word] packs a monomial over variables 1..56 into one immediate integer:
   bits 0..55 are the variables and bits 56..61 hold the degree, so plain
   integer comparison is already a graded order (degree first), equality and
   hashing are single machine operations, and the product of two monomials is
   a bitwise or plus a popcount. [Big] is the same idea on a Zarith bitset for
   instances with more variables. [for_vars] picks the representation. *)

module type S = sig
  type t

  val capacity : int (* largest variable index *)
  val one : t
  val var : int -> t
  val of_list : int list -> t
  val to_list : t -> int list (* increasing *)
  val degree : t -> int
  val mul : t -> t -> t (* union of the variable sets *)
  val mem : int -> t -> bool
  val disjoint : t -> t -> bool
  val subset : t -> t -> bool (* subset a b: a ⊆ b *)
  val compare : t -> t -> int (* graded: degree first *)
  val equal : t -> t -> bool
  val hash : t -> int
  val to_string : t -> string
end

let render vs = if vs = [] then "1" else String.concat "*" (List.map (fun v -> "x" ^ string_of_int v) vs)

module Word : S with type t = private int = struct
  type t = int

  let capacity = 56
  let shift = 56
  let mask = (1 lsl 56) - 1

  (* SWAR popcount of a 56-bit word; the multiplication may wrap, but only
     the low 56 bits matter and those are exact *)
  let popcount x =
    let x = x - ((x lsr 1) land 0x55555555555555) in
    let x = (x land 0x33333333333333) + ((x lsr 2) land 0x33333333333333) in
    let x = (x + (x lsr 4)) land 0x0f0f0f0f0f0f0f in
    ((x * 0x01010101010101) lsr 48) land 0xff

  let make bits = bits lor (popcount bits lsl shift)
  let one = 0

  let bit v =
    if v < 1 || v > capacity then invalid_arg (Printf.sprintf "Mono.Word: variable %d outside 1..56" v);
    1 lsl (v - 1)

  let var v = make (bit v)
  let of_list l = make (List.fold_left (fun b v -> b lor bit v) 0 l)

  let to_list t =
    let rec go v bits acc = if bits = 0 then List.rev acc else go (v + 1) (bits lsr 1) (if bits land 1 = 1 then v :: acc else acc) in
    go 1 (t land mask) []

  let degree t = t lsr shift
  let mul a b = make ((a lor b) land mask)
  let mem v t = v >= 1 && v <= capacity && (t lsr (v - 1)) land 1 = 1
  let disjoint a b = a land b land mask = 0
  let subset a b = a land mask land lnot b = 0
  let compare = Int.compare
  let equal = Int.equal
  let hash t = Hashtbl.hash t
  let to_string t = render (to_list t)
end

module Big : S = struct
  type t = { deg : int; bits : Z.t }

  let capacity = max_int
  let make bits = { deg = Z.popcount bits; bits }
  let one = { deg = 0; bits = Z.zero }

  let bit v =
    if v < 1 then invalid_arg (Printf.sprintf "Mono.Big: variable %d" v);
    Z.shift_left Z.one (v - 1)

  let var v = make (bit v)
  let of_list l = make (List.fold_left (fun b v -> Z.logor b (bit v)) Z.zero l)
  let to_list t = List.filter (fun v -> Z.testbit t.bits (v - 1)) (List.init (Z.numbits t.bits) (fun i -> i + 1))
  let degree t = t.deg
  let mul a b = make (Z.logor a.bits b.bits)
  let mem v t = v >= 1 && Z.testbit t.bits (v - 1)
  let disjoint a b = Z.equal (Z.logand a.bits b.bits) Z.zero
  let subset a b = Z.equal (Z.logand a.bits (Z.lognot b.bits)) Z.zero

  let compare a b =
    let c = Int.compare a.deg b.deg in
    if c <> 0 then c else Z.compare a.bits b.bits

  let equal a b = a.deg = b.deg && Z.equal a.bits b.bits
  let hash t = Z.hash t.bits
  let to_string t = render (to_list t)
end

let for_vars n : (module S) = if n <= Word.capacity then (module Word) else (module Big)

(* the canonical order of monomials in proof objects: by degree, then
   lexicographically on the sorted variable list *)
let compare_lists (a : int list) (b : int list) = compare (List.length a, a) (List.length b, b)
