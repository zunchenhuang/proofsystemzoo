(* Sherali–Adams: exact minimum-degree search through the certified LP, with
   feasible points (pseudo-expectations) as lower-bound certificates. Proof
   format sa/1:

     {"format": "sa/1", "terms": [{"ax": i | null, "S": [...], "T": [...], "coef": c}, ...]}

   Each term is c·J_{S,T}·(aᵢx − bᵢ) (or c·J_{S,T} when ax is null), with
   J_{S,T} = ∏_{S} x · ∏_{T} (1 − x) and c > 0; the terms must sum to a
   negative constant. The degree is max |S| + |T| (+1 with an axiom). A
   lower bound {"metric": "degree", "value": d, "point": [[[vars], "q"], ...]}
   gives z on monomials (z(1) = 1) that is non-negative on every product of
   degree d − 1, so no refutation of degree < d exists. *)
open System

let format = "sa/1"

type term = { ax : int option; s : int list; t : int list; coef : Z.t }
type proof = term list
type lower_bound = { degree : int; point : (int list * Q.t) list }

let term_codec : term Json.codec =
  let open Json in
  codec
    (fun t -> E.obj [ ("ax", E.nullable E.int t.ax); ("S", E.ints t.s); ("T", E.ints t.t); ("coef", E.z t.coef) ])
    (fun j ->
      let* ax = D.field_opt "ax" D.int j in
      let* s = D.field "S" (D.list D.int) j in
      let* t = D.field "T" (D.list D.int) j in
      let+ coef = D.field "coef" D.z j in
      { ax; s; t; coef })

let codec : proof Json.codec =
  let open Json in
  codec
    (fun terms -> E.obj [ ("format", `String format); ("terms", E.list term_codec.encode terms) ])
    (fun j ->
      let* () = D.tag "format" format j in
      D.field "terms" (D.list term_codec.decode) j)

let lower_bound_codec : lower_bound Json.codec =
  let open Json in
  codec
    (fun l -> E.obj [ ("metric", `String "degree"); ("value", `Int l.degree); ("point", (Algebraic.terms_codec q).encode l.point) ])
    (fun j ->
      let* () = D.tag "metric" "degree" j in
      let* degree = D.field "value" D.int j in
      let+ point = D.field "point" (Algebraic.terms_codec q).decode j in
      { degree; point })

(* the juntas J_{S,T} with |S| + |T| ≤ size: by size, variable set in
   lexicographic order, then every split of the set into S and T *)
let juntas n size : (int list * int list) Seq.t =
  Seq.flat_map
    (fun k ->
      Seq.flat_map
        (fun vs ->
          let arr = Array.of_list vs in
          Seq.map
            (fun signs ->
              let s = ref [] and t = ref [] in
              for i = k - 1 downto 0 do
                if (signs lsr (k - 1 - i)) land 1 = 0 then s := arr.(i) :: !s else t := arr.(i) :: !t
              done;
              (!s, !t))
            (Seqx.range 0 (1 lsl k)))
        (Seqx.combinations (Array.init n (fun i -> i + 1)) k))
    (Seqx.range 0 (size + 1))

let rec binom n k = if k < 0 || k > n then 0 else if k = 0 || k = n then 1 else binom (n - 1) (k - 1) * n / k
let count_juntas n size = List.fold_left ( + ) 0 (List.init (max 0 (size + 1)) (fun k -> binom n k * (1 lsl k)))
let count_products (sys : Ineq.t) d = (count_juntas sys.num_vars (d - 1) * Array.length sys.ineqs) + count_juntas sys.num_vars d - 1

module Algo (M : Mono.S) = struct
  module K = Field.Rational
  module R = Ring.Make (K) (M)

  module H = Hashtbl.Make (struct
    type t = M.t

    let equal = M.equal
    let hash = M.hash
  end)

  let junta s t =
    R.of_terms
      (List.of_seq
         (Seq.map (fun u -> (M.of_list (s @ u), if List.length u mod 2 = 0 then Q.one else Q.minus_one)) (Seqx.subsets_upto (Array.of_list t) (List.length t))))

  let linear (q : Ineq.ineq) = R.of_terms ((M.one, Q.of_int (-q.rhs)) :: List.map (fun (v, c) -> (M.var v, Q.of_int c)) q.terms)

  let product (sys : Ineq.t) ax s t =
    let j = junta s t in
    match ax with None -> j | Some i -> R.mul j (linear sys.ineqs.(i))

  (* every product of degree ≤ d, in a fixed order *)
  let products (sys : Ineq.t) d : (term * R.t) Seq.t =
    let n = sys.num_vars in
    Seq.append
      (Seq.flat_map
         (fun (s, t) ->
           let j = junta s t in
           Seq.map (fun i -> ({ ax = Some i; s; t; coef = Z.zero }, R.mul j (linear sys.ineqs.(i)))) (Seqx.range 0 (Array.length sys.ineqs)))
         (juntas n (d - 1)))
      (Seq.filter_map (fun (s, t) -> if s = [] && t = [] then None else Some ({ ax = None; s; t; coef = Z.zero }, junta s t)) (juntas n d))

  let measures (terms : proof) =
    Measures.(
      empty
      |> int "degree" (List.fold_left (fun d t -> max d (List.length t.s + List.length t.t + if t.ax = None then 0 else 1)) 0 terms)
      |> int "size" (List.length terms)
      |> big "max_coef" (List.fold_left (fun m t -> Z.max m t.coef) Z.zero terms))

  let search (lim : Limits.t) (sys : Ineq.t) =
    let n = sys.num_vars in
    let top = match lim.max_degree with None -> n + 1 | Some d -> min d (n + 1) in
    let max_rows = Limits.size lim 50_000 and deadline = Limits.deadline lim in
    let point = ref None and d = ref 1 in
    let lb refuted_at =
      match !point with
      | Some (dd, z) when refuted_at = None || refuted_at = Some (dd + 1) -> Some { degree = dd + 1; point = z }
      | _ -> None
    in
    let stop msg = unknown ~measures:Measures.(empty |> int "degree_lb" !d) ?lower_bound:(lb None) msg in
    let rec loop dd =
      if dd > top then
        if top = n + 1 then model (Printf.sprintf "no refutation at degree n+1=%d" top)
        else unknown ~measures:Measures.(empty |> int "degree_lb" (top + 1)) ?lower_bound:(lb None) (Printf.sprintf "no refutation of degree <= %d" top)
      else begin
        d := dd;
        let count = count_products sys dd in
        if count > max_rows then stop (Printf.sprintf "%d products at degree %d > max_size=%d" count dd max_rows)
        else begin
          let prods = Array.of_seq (products sys dd) in
          let ids = H.create 1024 and back = Vec.create M.one in
          let id m =
            match H.find_opt ids m with
            | Some i -> i
            | None ->
                let i = Vec.push back m in
                H.replace ids m i;
                i
          in
          let rows =
            Array.map
              (fun (_, (p : R.t)) ->
                let terms = ref [] and const = ref Q.zero in
                Array.iteri (fun q m -> if M.equal m M.one then const := p.R.cs.(q) else terms := (id m, p.R.cs.(q)) :: !terms) p.R.ms;
                (Array.of_list !terms, Q.neg !const))
              prods
          in
          match Lp.farkas ~deadline ~nvars:(Vec.length back) rows with
          | Lp.Certificate y ->
              let c = Num.integral y in
              let terms = List.filter_map (fun (k, (tm, _)) -> if Z.sign c.(k) = 0 then None else Some { tm with coef = c.(k) }) (List.mapi (fun k p -> (k, p)) (Array.to_list prods)) in
              refutation ?lower_bound:(lb (Some dd)) ~measures:(Measures.int "products" count (measures terms)) terms
          | Lp.Point z ->
              let pt = List.filter_map (fun i -> if Q.sign z.(i) = 0 then None else Some (M.to_list (Vec.get back i), z.(i))) (List.init (Vec.length back) Fun.id) in
              point := Some (dd, List.sort (fun (a, _) (b, _) -> Mono.compare_lists a b) pt);
              loop (dd + 1)
          | Lp.Undecided _ -> loop (dd + 1)
        end
      end
    in
    try loop 1 with Clock.Timeout -> stop budget_message

  let valid_sets n (t : term) =
    let all = t.s @ t.t in
    List.length (List.sort_uniq compare all) = List.length all && List.for_all (fun v -> v >= 1 && v <= n) all

  let verify (sys : Ineq.t) (terms : proof) =
    if terms = [] then Error "no terms"
    else
      let acc = H.create 1024 in
      let check t =
        if Z.sign t.coef <= 0 then Error "coefficient must be positive"
        else if not (valid_sets sys.num_vars t) then Error "S and T must be disjoint sets of known variables"
        else if match t.ax with Some i -> i < 0 || i >= Array.length sys.ineqs | None -> false then Error "no such input inequality"
        else begin
          let p = product sys t.ax (List.sort compare t.s) (List.sort compare t.t) and c = Q.of_bigint t.coef in
          Array.iteri (fun q m -> H.replace acc m (Q.add (Q.mul c p.R.cs.(q)) (Option.value (H.find_opt acc m) ~default:Q.zero))) p.R.ms;
          Ok ()
        end
      in
      match Seqx.iter_result check (List.to_seq terms) with
      | Error e -> Error e
      | Ok () -> (
          match H.fold (fun m c l -> if Q.sign c = 0 then l else (m, c) :: l) acc [] with
          | [ (m, c) ] when M.equal m M.one && Q.sign c < 0 -> Ok (measures terms)
          | _ -> Error "the terms do not sum to a negative constant")

  let check_lower_bound (sys : Ineq.t) (l : lower_bound) =
    let dd = l.degree - 1 in
    if dd < 1 then Error "degree must be at least 2"
    else if List.exists (fun (vs, _) -> not (Algebraic.check_mono sys.num_vars vs)) l.point then Error "malformed monomial in point"
    else begin
      let z = H.create 1024 in
      List.iter (fun (vs, v) -> H.replace z (M.of_list vs) v) l.point;
      H.replace z M.one Q.one;
      let value m = Option.value (H.find_opt z m) ~default:Q.zero in
      if Seq.for_all (fun (_, p) -> Q.sign (R.apply value p) >= 0) (products sys dd) then Ok Measures.(empty |> int "degree_lb_certified" (dd + 1))
      else Error "the point violates a product inequality"
    end
end

module type ALGO = sig
  val search : Limits.t -> Ineq.t -> (proof, lower_bound) outcome
  val verify : Ineq.t -> proof -> (Measures.t, string) result
  val check_lower_bound : Ineq.t -> lower_bound -> (Measures.t, string) result
end

let with_algo (sys : Ineq.t) f =
  let (module M) = Mono.for_vars sys.num_vars in
  f (module Algo (M) : ALGO)

type config = unit
type input = Ineq.t

let name = "sherali-adams"
let version = "0.3"

let info =
  {
    group = "semialgebraic";
    order = 100;
    line_type = "linear inequality (lifted)";
    primary_metric = "degree";
    book = "6.4";
    simulates = [];
    description = "Sherali–Adams; exact minimum-degree search via certified LP, points as lower bounds";
  }

let language = Lang.Ineq
let encoding = Some "cnf-ineq"
let params = []
let variants = [ [] ]
let label _ = "SA"
let configure _ = Ok ()
let searches () = true
let search () lim sys = with_algo sys (fun (module A) -> A.search lim sys)
let proof = codec
let lower_bound = lower_bound_codec
let verify () sys p = with_algo sys (fun (module A) -> A.verify sys p)
let check_lower_bound () sys l = with_algo sys (fun (module A) -> A.check_lower_bound sys l)
let parse_text = None
