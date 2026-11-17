(** Language ["ineq"]: systems of linear inequalities Σ aᵢxᵢ ≥ b over 0/1
    variables, with integer coefficients (OPB text). Canonical and private,
    like {!Cnf}. *)

type ineq = private { terms : (int * int) list; rhs : int }
(** terms sorted by variable, coefficients non-zero *)

type t = private { num_vars : int; ineqs : ineq array; names : (int * string) list }

val make_ineq : (int * int) list -> int -> ineq
val make : ?num_vars:int -> ?names:(int * string) list -> ineq list -> t
val holds : ineq -> Assignment.t -> bool
val eval : t -> Assignment.t -> bool
val to_text : ?comments:bool -> t -> string
val of_text : string -> (t, string) result
val sha256 : t -> string
val ineq_to_string : ineq -> string
val max_width : t -> int
