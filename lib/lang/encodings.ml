(* Encodings: named, deterministic translations between languages. An
   encoding of type [('a, 'b) t] maps instances of type ['a] to ['b], and
   carries the language witnesses of both sides; [convert] uses them to find
   a translation for a packed problem and returns a value of exactly the type
   the caller asked for. *)

type ('a, 'b) t = { name : string; source : 'a Lang.t; target : 'b Lang.t; description : string; run : 'a -> 'b }
type any = Any : ('a, 'b) t -> any

(* ∏_{x∈C⁺}(1−x) · ∏_{¬y∈C⁻} y: equal to 1 exactly on the assignments falsifying C *)
let clause_indicator (c : Clause.t) : Poly.poly =
  let lits = Clause.lits c in
  let pos = List.filter (fun l -> l > 0) lits and neg = List.map abs (List.filter (fun l -> l < 0) lits) in
  Seqx.subsets_upto (Array.of_list pos) (List.length pos)
  |> Seq.map (fun s -> (List.sort_uniq compare (s @ neg), if List.length s mod 2 = 0 then 1 else -1))
  |> List.of_seq |> Poly.make_poly

let cnf_poly : (Cnf.t, Poly.t) t =
  {
    name = "cnf-poly";
    source = Lang.Cnf;
    target = Lang.Poly;
    description = "clause C ↦ ∏(1−x)·∏y = 0 (falsifier indicator); Boolean axioms implicit";
    run =
      (fun c ->
        Poly.make ~num_vars:c.Cnf.num_vars ~names:c.Cnf.names
          (List.filter (fun p -> Poly.terms p <> []) (Array.to_list (Array.map clause_indicator c.Cnf.clauses))));
  }

let cnf_poly_twin : (Cnf.t, Poly.t) t =
  {
    name = "cnf-poly-twin";
    source = Lang.Cnf;
    target = Lang.Poly;
    description = "PCR encoding: twin x̄ᵢ = x_{n+i}; clause ↦ monomial ∏x̄·∏y = 0; axioms x + x̄ − 1 = 0";
    run =
      (fun c ->
        let n = c.Cnf.num_vars in
        let bar v = n + v in
        let clauses =
          Array.to_list c.Cnf.clauses
          |> List.map (fun cl -> Poly.make_poly [ (List.map (fun l -> if l > 0 then bar l else -l) (Clause.lits cl), 1) ])
        in
        let complements = List.init n (fun i -> Poly.make_poly [ ([ i + 1 ], 1); ([ bar (i + 1) ], 1); ([], -1) ]) in
        let names =
          c.Cnf.names
          @ List.init n (fun i ->
                let v = i + 1 in
                (bar v, "~" ^ Option.value (List.assoc_opt v c.Cnf.names) ~default:(Printf.sprintf "x%d" v)))
        in
        Poly.make ~num_vars:(2 * n) ~names (clauses @ complements));
  }

let cnf_ineq : (Cnf.t, Ineq.t) t =
  {
    name = "cnf-ineq";
    source = Lang.Cnf;
    target = Lang.Ineq;
    description = "clause C ↦ Σ_{x∈C⁺} x + Σ_{¬y∈C⁻} (1 − y) ≥ 1";
    run =
      (fun c ->
        Array.to_list c.Cnf.clauses
        |> List.map (fun cl ->
               let lits = Clause.lits cl in
               Ineq.make_ineq (List.map (fun l -> (abs l, if l > 0 then 1 else -1)) lits) (1 - List.length (List.filter (fun l -> l < 0) lits)))
        |> Ineq.make ~num_vars:c.Cnf.num_vars ~names:c.Cnf.names);
  }

(* the inverse of cnf-ineq on clause-shaped inequalities *)
let ineq_as_clause (q : Ineq.ineq) : Clause.t option =
  if List.exists (fun (_, c) -> c <> 1 && c <> -1) q.terms then None
  else if q.rhs <> 1 - List.length (List.filter (fun (_, c) -> c < 0) q.terms) then None
  else Some (Clause.of_list (List.map (fun (v, c) -> if c > 0 then v else -v) q.terms))

let all = [ Any cnf_poly; Any cnf_poly_twin; Any cnf_ineq ]
let find name = List.find_opt (fun (Any e) -> e.name = name) all

let describe (Any e) = (e.name, Lang.name e.source, Lang.name e.target, e.description)

(* can an instance of language [src] reach language [target]? *)
let reachable (Lang.Any src) (Lang.Any target) =
  Lang.name src = Lang.name target
  || List.exists (fun (Any e) -> Lang.name e.source = Lang.name src && Lang.name e.target = Lang.name target) all

(* Convert a packed problem into language [target]; with [prefer], that
   encoding is tried first. Returns the value and the encoding used. *)
let convert : type b. ?prefer:string -> b Lang.t -> Lang.problem -> (b * string option, string) result =
 fun ?prefer target p ->
  match p with
  | Lang.Problem (src, x) -> (
      match Lang.equal src target with
      | Some Lang.Refl -> Ok (x, None)
      | None -> (
          (* the two equations refine e's existential source to x's type and
             its target to b, so [e.run x : b] *)
          let attempt (Any e) : (b * string option) option =
            match (Lang.equal e.source src, Lang.equal e.target target) with
            | Some Lang.Refl, Some Lang.Refl -> Some (e.run x, Some e.name)
            | _ -> None
          in
          let preferred = match prefer with Some n -> Option.to_list (find n) | None -> [] in
          match List.find_map attempt (preferred @ all) with
          | Some r -> Ok r
          | None -> Error (Printf.sprintf "no encoding from %s to %s" (Lang.name src) (Lang.name target))))
