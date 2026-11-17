(* Shared pieces of the algebraic systems over GF(p). *)

(* a prime field whose elements are machine integers *)
module type GF = sig
  include Field.S with type t = private int

  val to_int : t -> int
end

let field_of_env env : (module GF) =
  let p = Param.get_int env "p" in
  (module Field.Gf (struct
    let p = p
  end))

let p_param = Param.prime ~key:"p" ~default:2 ()

(* monomials and coefficients as they appear in proof objects *)
let mono_codec : int list Json.codec = Json.codec Json.E.ints (Json.D.list Json.D.int)
let terms_codec (c : 'a Json.codec) : (int list * 'a) list Json.codec = Json.list (Json.pair mono_codec c)

(* a monomial from a proof: distinct variables in range *)
let check_mono n (vs : int list) =
  List.for_all (fun v -> v >= 1 && v <= n) vs && List.length (List.sort_uniq compare vs) = List.length vs

(* the variables of 1..n that are not absorbing for f (x·f ∉ {0, f}) *)
let free_vars n absorbing = Array.of_list (List.filter (fun v -> not (List.mem v absorbing)) (List.init n (fun i -> i + 1)))
