(** Language ["poly"]: systems of multilinear polynomial equations f = 0
    over 0/1 variables, integer coefficients (systems reduce them in their
    own field). The Boolean axioms x² = x are implicit. Canonical and
    private, like {!Cnf}. *)

type mono = int list
(** sorted, distinct variables; [] is the constant 1 *)

type poly = private (mono * int) list
(** sorted by (degree, monomial), non-zero coefficients *)

type t = private { num_vars : int; polys : poly array; names : (int * string) list }

val make_poly : (int list * int) list -> poly
val make : ?num_vars:int -> ?names:(int * string) list -> poly list -> t
val terms : poly -> (mono * int) list
val degree : poly -> int
val vars : poly -> int list
val eval_poly : poly -> Assignment.t -> int
val eval : t -> Assignment.t -> bool
val to_text : ?comments:bool -> t -> string
val of_text : string -> (t, string) result
val sha256 : t -> string
val max_degree : t -> int
