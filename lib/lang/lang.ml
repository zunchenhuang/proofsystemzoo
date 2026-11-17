(* The input languages, as a GADT: a value of type ['a t] is a witness that
   instances of that language have OCaml type ['a]. Systems declare the
   language they read by such a witness, encodings are typed by a pair of
   witnesses, and [equal] recovers type equality at run time, so an instance
   can only reach a system after it has been converted to exactly the type
   that system's search and verifier expect. *)

type _ t = Cnf : Cnf.t t | Poly : Poly.t t | Ineq : Ineq.t t
type (_, _) eq = Refl : ('a, 'a) eq
type any = Any : 'a t -> any
type problem = Problem : 'a t * 'a -> problem

let equal : type a b. a t -> b t -> (a, b) eq option =
 fun a b -> match (a, b) with Cnf, Cnf -> Some Refl | Poly, Poly -> Some Refl | Ineq, Ineq -> Some Refl | _ -> None

let name : type a. a t -> string = function Cnf -> "cnf" | Poly -> "poly" | Ineq -> "ineq"
let all = [ Any Cnf; Any Poly; Any Ineq ]
let names = List.map (fun (Any l) -> name l) all
let of_name s = List.find_opt (fun (Any l) -> name l = s) all

let to_text : type a. a t -> a -> string =
 fun l x -> match l with Cnf -> Cnf.to_dimacs x | Poly -> Poly.to_text x | Ineq -> Ineq.to_text x

let of_text : type a. a t -> string -> (a, string) result =
 fun l s -> match l with Cnf -> Cnf.of_dimacs s | Poly -> Poly.of_text s | Ineq -> Ineq.of_text s

let sha256 : type a. a t -> a -> string =
 fun l x -> match l with Cnf -> Cnf.sha256 x | Poly -> Poly.sha256 x | Ineq -> Ineq.sha256 x

let num_vars : type a. a t -> a -> int =
 fun l x -> match l with Cnf -> x.Cnf.num_vars | Poly -> x.Poly.num_vars | Ineq -> x.Ineq.num_vars

(* (variables, constraints, max width or degree) *)
let stats : type a. a t -> a -> int * int * int =
 fun l x ->
  match l with
  | Cnf -> (x.Cnf.num_vars, Cnf.num_clauses x, Cnf.max_width x)
  | Poly -> (x.Poly.num_vars, Array.length x.Poly.polys, Poly.max_degree x)
  | Ineq -> (x.Ineq.num_vars, Array.length x.Ineq.ineqs, Ineq.max_width x)

let eval : type a. a t -> a -> Assignment.t -> bool =
 fun l x a -> match l with Cnf -> Cnf.eval x a | Poly -> Poly.eval x a | Ineq -> Ineq.eval x a

(* --- the same operations on packed problems *)
let problem_name (Problem (l, _)) = name l
let problem_text (Problem (l, x)) = to_text l x
let problem_sha256 (Problem (l, x)) = sha256 l x
let problem_vars (Problem (l, x)) = num_vars l x
let problem_stats (Problem (l, x)) = stats l x
let problem_eval (Problem (l, x)) a = eval l x a

let parse (lang : string) (text : string) : (problem, string) result =
  match of_name lang with
  | Some (Any l) -> Result.map (fun x -> Problem (l, x)) (of_text l text)
  | None -> Error (Printf.sprintf "unknown language %s (known: %s)" lang (String.concat ", " names))

(* exhaustive check, for tiny instances in tests *)
let brute_force_sat (p : problem) =
  let n = problem_vars p in
  if n > 22 then invalid_arg "brute force limited to 22 variables";
  Seq.exists (problem_eval p) (Assignment.all n)
