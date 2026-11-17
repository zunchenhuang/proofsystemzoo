(** Clauses in canonical form.

    A clause is a set of non-zero DIMACS literals, stored sorted by variable
    (a negative literal before the positive one) without duplicates. The type
    is private: clauses are built only by {!of_list}, {!of_list_strict} and
    {!resolve}, so every clause in the program satisfies the invariant and
    can be compared, hashed and merged without re-normalising. *)

type t = private int array

val of_list : int list -> t
(** Canonicalises (sorts, removes duplicates). Raises [Invalid_argument] on 0. *)

val of_list_strict : int list -> (t, string) result
(** For decoding proofs: rejects 0 and duplicate literals instead of fixing them. *)

val empty : t
val lits : t -> int list
val width : t -> int
val is_empty : t -> bool
val mem : int -> t -> bool
val is_tautology : t -> bool

val max_var : t -> int
(** largest variable index (0 for the empty clause) *)

val resolve : t -> t -> int -> t
(** [resolve a b v] is (a \ {v}) ∪ (b \ {-v}); the caller ensures [v ∈ a] and [-v ∈ b]. *)

val subset : t -> t -> bool

val compare : t -> t -> int
(** canonical order: by width, then lexicographically on the literal sequence *)

val equal : t -> t -> bool
val hash : t -> int
val to_string : t -> string
val codec : t Json.codec

module Tbl : Hashtbl.S with type key = t
