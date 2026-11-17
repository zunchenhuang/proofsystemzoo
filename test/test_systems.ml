(* Property tests of the systems on random small formulas: soundness (no
   verified refutation of a satisfiable formula, witnesses satisfy),
   completeness on unsatisfiable ones, relations between systems, the
   encodings, and tampering (each verifier rejects broken proofs). *)
open Proofsystemzoo
open Check

type verdict =
  | Refuted of { verified : (Measures.t, string) result; lb : (Measures.t, string) result option; measures : Measures.t }
  | Sat of bool option (* did the witness satisfy the original formula *)
  | Open of { lb : (Measures.t, string) result option; message : string }
  | Na

(* search, send the outcome through its JSON codec, check what came back *)
let run (inst : System.instance) (problem : Lang.problem) =
  let (module I : System.INSTANCE) = inst in
  let module S = I.S in
  match Encodings.convert ?prefer:S.encoding S.language problem with
  | Error _ -> Na
  | Ok (input, _) -> (
      let limits = Limits.with_time (Some 20.0) Limits.none in
      let o = S.search I.config limits input in
      let o = match Json.roundtrip (System.outcome_codec S.proof S.lower_bound) o with Ok o -> o | Error e -> failwith ("outcome roundtrip: " ^ e) in
      let lb = Option.map (S.check_lower_bound I.config input) in
      match o with
      | System.Refutation r -> (
          (* the proof itself must survive its codec unchanged *)
          match Json.roundtrip S.proof r.proof with
          | Error e -> failwith ("proof roundtrip: " ^ e)
          | Ok p -> Refuted { verified = S.verify I.config input p; lb = lb r.lower_bound; measures = Measures.union r.measures (Result.value ~default:Measures.empty (S.verify I.config input p)) })
      | System.Model m -> Sat (Option.map (Lang.problem_eval problem) m.witness)
      | System.Unknown u -> Open { lb = lb u.lower_bound; message = u.message })

let random_cnf st =
  let n = 2 + Random.State.int st 5 in
  let m = 2 + Random.State.int st 14 in
  let clause () =
    let w = 1 + Random.State.int st 3 in
    List.sort_uniq compare (List.init w (fun _ -> let v = 1 + Random.State.int st n in if Random.State.bool st then v else -v))
  in
  let cls = List.filter (fun c -> not (List.exists (fun l -> List.mem (-l) c) c)) (List.init m (fun _ -> clause ())) in
  Lang.Problem (Lang.Cnf, Cnf.of_lists ~num_vars:n cls)

let test_random_formulas () =
  let st = rng 11 in
  let instances = Registry.default_instances () in
  let unsat_seen = ref 0 and sat_seen = ref 0 in
  for k = 1 to 120 do
    let p = random_cnf st in
    let unsat = not (Lang.brute_force_sat p) in
    if unsat then incr unsat_seen else incr sat_seen;
    let degree = Hashtbl.create 16 and size = Hashtbl.create 16 in
    List.iter
      (fun inst ->
        let id = System.instance_id inst in
        let name = Printf.sprintf "formula %d, %s" k id in
        match run inst p with
        | Na -> ()
        | Refuted r ->
            ok (name ^ ": refutation verifies") r.verified;
            check (name ^ ": refuted only if unsatisfiable") unsat;
            Option.iter (ok (name ^ ": lower bound checks")) r.lb;
            Option.iter (fun d -> Hashtbl.replace degree id d) (Measures.find_int "degree" r.measures);
            Option.iter (fun s -> Hashtbl.replace size id s) (Measures.find_int "size" r.measures);
            (match (r.lb, Measures.find_int "degree" r.measures) with
            | Some (Ok m), Some d -> check (name ^ ": certified bound below the found degree") (Option.value (Measures.find_int "degree_lb_certified" m) ~default:0 <= d)
            | _ -> ())
        | Sat w ->
            check (name ^ ": satisfiable only if satisfiable") (not unsat);
            check (name ^ ": witness satisfies") (w <> Some false)
        | Open o ->
            Option.iter (ok (name ^ ": lower bound checks")) o.lb;
            check (name ^ ": complete on a tiny unsatisfiable formula (" ^ o.message ^ ")") (not unsat))
      instances;
    (* relations between systems *)
    if unsat then begin
      let d id = Hashtbl.find_opt degree id and s id = Hashtbl.find_opt size id in
      let le a b = match (a, b) with Some x, Some y -> x <= y | _ -> true in
      check "PC degree ≤ NS degree" (le (d "polynomial-calculus[p=2]") (d "nullstellensatz[p=2]") && le (d "polynomial-calculus[p=3]") (d "nullstellensatz[p=3]"));
      check "PCR degree ≤ PC degree" (le (d "pcr[p=2]") (d "polynomial-calculus[p=2]"));
      check "DAG size ≤ tree and ordered size" (le (s "resolution") (s "tree-resolution") && le (s "resolution") (s "ordered-resolution"))
    end
  done;
  check "the sample has both kinds of formulas" (!unsat_seen > 15 && !sat_seen > 15)

(* the encodings preserve satisfying assignments *)
let test_encodings () =
  let st = rng 12 in
  for _ = 1 to 100 do
    let cnf : Cnf.t option = match random_cnf st with Lang.Problem (Lang.Cnf, c) -> Some c | _ -> None in
    match cnf with
    | Some c ->
        let n = c.num_vars in
        let poly = Encodings.cnf_poly.run c and twin = Encodings.cnf_poly_twin.run c and ineq = Encodings.cnf_ineq.run c in
        Seq.iter
          (fun a ->
            let sat = Cnf.eval c a in
            check "cnf-poly" (Poly.eval poly a = sat);
            check "cnf-ineq" (Ineq.eval ineq a = sat);
            let a2 = Assignment.make (2 * n) (fun v -> if v <= n then Assignment.get a v else not (Assignment.get a (v - n))) in
            check "cnf-poly-twin" (Poly.eval twin a2 = sat))
          (Assignment.all n);
        check "ineq-as-clause inverts cnf-ineq"
          (let back = Array.to_list (Array.map Encodings.ineq_as_clause ineq.ineqs) in
           List.for_all Option.is_some back
           && List.sort Clause.compare (List.map Option.get back) = List.sort Clause.compare (Array.to_list c.clauses))
    | None -> ()
  done

(* --------------------------------------------------------------- tampering *)
let php32 : Cnf.t = match (Families.php 2).problem with Lang.Problem (Lang.Cnf, c) -> c | _ -> assert false
let poly32 = Encodings.cnf_poly.run php32
let ineq32 = Encodings.cnf_ineq.run php32
let lim = Limits.with_time (Some 20.0) Limits.none
let env params given = Result.get_ok (Param.resolve params given)

let proof_of name = function System.Refutation r -> r.proof | _ -> failwith (name ^ ": no refutation of php-3-2")

let test_tampering () =
  (* truth table: point an assignment at a clause it satisfies *)
  let tt = proof_of "truth-table" (Truth_table.search () lim php32) in
  ok "truth table verifies" (Truth_table.verify () php32 tt);
  let bad = Array.copy tt in
  let pats = Array.map Truth_table.pattern php32.clauses in
  bad.(0) <- (let k = ref 0 in while (let m, v = pats.(!k) in 0 land m = v) do incr k done; !k);
  err "truth table: wrong clause rejected" (Truth_table.verify () php32 bad);
  (* resolution: drop the final empty clause; change a derived clause *)
  let res = proof_of "resolution" (Resolution.Dag.search () lim php32) in
  ok "resolution verifies" (Resolution.Dag.verify () php32 res);
  let n = Array.length res.lines in
  err "resolution: truncated proof rejected" (Resolution.Dag.verify () php32 { res with lines = Array.sub res.lines 0 (n - 1) });
  let k = (let k = ref (n - 1) in while res.lines.(!k).rule = Resolution.Axiom do decr k done; !k) in
  let forged = Array.copy res.lines in
  forged.(k) <- { (forged.(k)) with clause = Clause.of_list [ 1 ] };
  err "resolution: forged resolvent rejected" (Resolution.Dag.verify () php32 { res with lines = forged });
  (* tree-like: a DAG proof that reuses a line is not tree-like *)
  let reuse = ref false in
  Array.iteri (fun i l -> match l.Resolution.rule with Resolution.Res r -> Array.iteri (fun j l' -> if j > i then match l'.Resolution.rule with Resolution.Res r' when r'.pos = r.pos || r'.neg = r.neg -> if res.lines.(r.pos).rule <> Resolution.Axiom then reuse := true | _ -> () ) res.lines | _ -> ()) res.lines;
  if !reuse then err "tree-resolution: reused line rejected" (Resolution.Tree.verify () php32 res);
  (* DRAT: without its lemmas the empty clause is not RUP *)
  let drat = proof_of "drat" (Drat.search () lim php32) in
  ok "drat verifies" (Drat.verify () php32 drat);
  err "drat: lemmas removed" (Drat.verify () php32 [ Drat.Add [||] ]);
  (match Drat.parse_drat "c a comment\n1 2 0\nd 1 2 0\n0\n" with
  | Ok [ Drat.Add [| 1; 2 |]; Drat.Delete [| 1; 2 |]; Drat.Add [||] ] -> incr passed
  | _ -> fail "drat text" "parse");
  (* RAT: a clause on a fresh variable is RAT on that variable, not on another *)
  let two = Cnf.of_lists ~num_vars:3 [ [ 1; 2 ]; [ -1; 2 ]; [ 1; -2 ]; [ -1; -2 ] ] in
  ok "drat: RAT on a fresh literal" (Drat.check two [ Drat.Add [| 3; 1 |]; Drat.Add [| 2 |]; Drat.Add [||] ]);
  err "drat: not RUP and not RAT on its first literal" (Drat.check (Cnf.of_lists ~num_vars:3 [ [ 1; 2 ]; [ -1; 2 ] ]) [ Drat.Add [| 1; 3 |]; Drat.Add [||] ]);
  (* Nullstellensatz: bump one coefficient *)
  let ns_cfg = Result.get_ok (Nullstellensatz.configure (env Nullstellensatz.params [ ("p", "3") ])) in
  let ns = proof_of "nullstellensatz" (Nullstellensatz.search ns_cfg lim poly32) in
  ok "ns verifies" (Nullstellensatz.verify ns_cfg poly32 ns);
  let t = List.hd ns.terms in
  let bumped = { t with mult = (match t.mult with (m, c) :: r -> (m, (c + 1) mod 3) :: r | [] -> []) } in
  err "ns: bumped coefficient rejected" (Nullstellensatz.verify ns_cfg poly32 { ns with terms = bumped :: List.tl ns.terms });
  err "ns: wrong field rejected" (Nullstellensatz.verify ns_cfg poly32 { ns with p = 5 });
  (* NS lower bound: a design that is wrong somewhere is rejected *)
  (match Nullstellensatz.search ns_cfg (Limits.with_time (Some 20.0) { Limits.none with max_degree = Some 2 }) poly32 with
  | System.Unknown { lower_bound = Some l; _ } ->
      ok "ns design checks" (Nullstellensatz.check_lower_bound ns_cfg poly32 l);
      let broken = { l with design = List.map (fun (m, c) -> if m = [] then (m, c) else (m, (c + 1) mod 3)) l.design } in
      err "ns: broken design rejected" (Nullstellensatz.check_lower_bound ns_cfg poly32 broken)
  | _ -> fail "ns" "expected a lower-bound certificate below the minimum degree");
  (* Polynomial Calculus: change a linear-combination coefficient *)
  let pc_cfg = Result.get_ok (Polycalc.Pc.configure (env Polycalc.Pc.params [ ("p", "2") ])) in
  let pc = proof_of "pc" (Polycalc.Pc.search pc_cfg lim poly32) in
  ok "pc verifies" (Polycalc.Pc.verify pc_cfg poly32 pc);
  err "pc: truncated proof rejected" (Polycalc.Pc.verify pc_cfg poly32 { pc with lines = Array.sub pc.lines 0 (Array.length pc.lines - 1) |> fun l -> if Array.length l = 0 then [| Polycalc.Axiom 0 |] else l });
  (* Cutting Planes: an addition with a doubled coefficient no longer cancels *)
  let cp = proof_of "cutting-planes" (Cutting_planes.search () lim ineq32) in
  ok "cp verifies" (Cutting_planes.verify () ineq32 cp);
  let last = Array.length cp - 1 in
  let doubled = Array.copy cp in
  (match cp.(last) with Cutting_planes.Add ((j, c) :: r) -> doubled.(last) <- Cutting_planes.Add ((j, Z.mul c (Z.of_int 2)) :: r) | _ -> ());
  err "cp: doubled coefficient rejected" (Cutting_planes.verify () ineq32 doubled);
  err "cp: division that does not divide" (Cutting_planes.verify () ineq32 [| Cutting_planes.Axiom 0; Cutting_planes.Div (0, Z.of_int 2) |]);
  (* Sherali–Adams: double one term *)
  let sa = proof_of "sherali-adams" (Sherali_adams.search () lim ineq32) in
  ok "sa verifies" (Sherali_adams.verify () ineq32 sa);
  err "sa: doubled term rejected" (Sherali_adams.verify () ineq32 ({ (List.hd sa) with coef = Z.mul (List.hd sa).coef (Z.of_int 2) } :: List.tl sa));
  (* Sum-of-Squares: scale a square; a DSOS check refuses general squares *)
  let sos = proof_of "sum-of-squares" (Sos.search Sos.Sos lim poly32) in
  ok "sos verifies" (Sos.verify Sos.Sos poly32 sos);
  let sq = List.hd sos.squares in
  err "sos: scaled square rejected" (Sos.verify Sos.Sos poly32 { sos with squares = { sq with c = Q.mul sq.c (Q.of_int 2) } :: List.tl sos.squares });
  err "sos: negative weight rejected" (Sos.verify Sos.Sos poly32 { sos with squares = { sq with c = Q.neg sq.c } :: List.tl sos.squares });
  let dsos = proof_of "dsos" (Sos.search Sos.Dsos lim poly32) in
  ok "dsos verifies" (Sos.verify Sos.Dsos poly32 dsos);
  if List.exists (fun s -> List.length s.Sos.s > 2) sos.squares then err "dsos: general squares rejected" (Sos.verify Sos.Dsos poly32 sos)

let () =
  case "random formulas" test_random_formulas;
  case "encodings" test_encodings;
  case "tampering" test_tampering;
  finish "systems"
