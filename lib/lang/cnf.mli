(** Language ["cnf"]: propositional formulas in conjunctive normal form.

    Instances are canonical (clauses sorted by {!Clause.compare}, no
    duplicates), so equal formulas have equal DIMACS text and equal content
    hashes. The record is private: instances are built by {!make},
    {!of_lists} or {!of_dimacs}. *)

type t = private { num_vars : int; clauses : Clause.t array; names : (int * string) list }

val make : ?num_vars:int -> ?names:(int * string) list -> Clause.t list -> t
(** Raises [Invalid_argument] if a literal exceeds [num_vars]. *)

val of_lists : ?num_vars:int -> ?names:(int * string) list -> int list list -> t
val num_clauses : t -> int
val max_width : t -> int
val to_dimacs : ?comments:bool -> t -> string
val of_dimacs : string -> (t, string) result
val sha256 : t -> string
val eval : t -> Assignment.t -> bool

val clause_set : t -> int Clause.Tbl.t
(** clause ↦ its index in [clauses] *)
