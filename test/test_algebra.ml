(* Unit and property tests of the algebra layer: monomials, fields,
   polynomials, echelon bases, the LP and SDP kernels, JSON codecs. *)
open Proofsystemzoo
open Check

let random_set st n k = List.sort_uniq compare (List.init k (fun _ -> 1 + Random.State.int st n))

(* ---------------------------------------------------------------- monomials *)
let test_monomials () =
  let st = rng 1 in
  let module W = Mono.Word in
  let module B = Mono.Big in
  for _ = 1 to 2000 do
    let a = random_set st 56 (Random.State.int st 12) and b = random_set st 56 (Random.State.int st 12) in
    let wa = W.of_list a and wb = W.of_list b and ba = B.of_list a and bb = B.of_list b in
    let union = List.sort_uniq compare (a @ b) in
    check "word roundtrip" (W.to_list wa = a);
    check "word degree" (W.degree wa = List.length a);
    check "word mul is union" (W.to_list (W.mul wa wb) = union && W.degree (W.mul wa wb) = List.length union);
    check "word graded order" (if List.length a <> List.length b then compare (List.length a) (List.length b) = compare (W.compare wa wb) 0 else true);
    check "word disjoint" (W.disjoint wa wb = not (List.exists (fun v -> List.mem v b) a));
    check "word subset" (W.subset wa wb = List.for_all (fun v -> List.mem v b) a);
    check "big agrees with word" (compare (W.compare wa wb) 0 = compare (B.compare ba bb) 0 && B.to_list (B.mul ba bb) = union)
  done;
  (* Big handles variables beyond 56 *)
  let x = B.of_list [ 3; 70; 200 ] in
  check "big beyond 56" (B.degree x = 3 && B.mem 200 x && not (B.mem 71 x));
  check "word rejects 57" (match W.var 57 with _ -> false | exception Invalid_argument _ -> true)

(* ---------------------------------------------------------------- fields *)
let test_fields () =
  let st = rng 2 in
  List.iter
    (fun p ->
      let module K = Field.Gf (struct
        let p = p
      end) in
      for _ = 1 to 500 do
        let a = K.of_int (Random.State.int st 1_000_000 - 500_000) and b = K.of_int (Random.State.int st 1_000_000) in
        check "gf sub/add" (K.equal (K.sub (K.add a b) b) a);
        check "gf inverse" (K.is_zero a || K.is_one (K.mul a (K.inv a)));
        check "gf neg" (K.is_zero (K.add a (K.neg a)));
        check "gf distributive" (K.equal (K.mul a (K.add b K.one)) (K.add (K.mul a b) a))
      done)
    [ 2; 3; 5; 7; 1_000_003 ];
  check "gf rejects composite"
    (try
       let module K = Field.Gf (struct
         let p = 9
       end) in
       ignore K.zero;
       false
     with Invalid_argument _ -> true)

(* ------------------------------------------------- polynomials on the cube *)
module K3 = Field.Gf (struct
  let p = 3
end)

module R = Ring.Make (K3) (Mono.Word)
module E = Echelon.Make (R)

let random_poly st n =
  R.of_terms (List.init (1 + Random.State.int st 6) (fun _ -> (Mono.Word.of_list (random_set st n (Random.State.int st 4)), K3.of_int (Random.State.int st 3))))

(* evaluation at a 0/1 point is a ring homomorphism of the multilinear ring *)
let eval (f : R.t) (a : bool array) =
  List.fold_left (fun s (m, c) -> if List.for_all (fun v -> a.(v)) (Mono.Word.to_list m) then K3.add s c else s) K3.zero (R.terms f)

let test_ring () =
  let st = rng 3 and n = 7 in
  for _ = 1 to 400 do
    let f = random_poly st n and g = random_poly st n and x = 1 + Random.State.int st n in
    let c = K3.of_int (1 + Random.State.int st 2) in
    let pts = List.init 12 (fun _ -> Array.init (n + 1) (fun _ -> Random.State.bool st)) in
    check "axpy on the cube" (List.for_all (fun a -> K3.equal (eval (R.axpy c f g) a) (K3.add (K3.mul c (eval f a)) (eval g a))) pts);
    check "mul on the cube" (List.for_all (fun a -> K3.equal (eval (R.mul f g) a) (K3.mul (eval f a) (eval g a))) pts);
    check "mul_var = mul_mono = mul" (R.equal (R.mul_var x f) (R.mul_mono (Mono.Word.var x) f) && R.equal (R.mul_var x f) (R.mul (R.monomial (Mono.Word.var x) K3.one) f));
    check "idempotent variable" (R.equal (R.mul_var x (R.mul_var x f)) (R.mul_var x f));
    check "sorted decreasing" (let ms = f.R.ms in Array.for_all Fun.id (Array.init (max 0 (Array.length ms - 1)) (fun i -> Mono.Word.compare ms.(i) ms.(i + 1) > 0)));
    check "absorbing" (List.for_all (fun v -> let xf = R.mul_var v f in R.is_zero xf || R.equal xf f) (R.absorbing f))
  done

let test_echelon () =
  let st = rng 4 and n = 6 in
  for _ = 1 to 60 do
    let gens = Array.init (5 + Random.State.int st 10) (fun _ -> random_poly st n) in
    let e = E.create () in
    Array.iteri (fun i g -> ignore (E.add e g ~gen:i)) gens;
    let coeffs = Array.map (fun _ -> K3.of_int (Random.State.int st 3)) gens in
    let target = Array.fold_left (fun acc (g, c) -> R.axpy c g acc) R.zero (Array.map2 (fun g c -> (g, c)) gens coeffs) in
    (match E.express e target with
    | None -> fail "express" "target in the span was not expressed"
    | Some combo -> check "express reconstructs the target" (R.equal (List.fold_left (fun acc (i, c) -> R.axpy c gens.(i) acc) R.zero combo) target));
    if not (E.spans_one e) then
      match E.design e with
      | None -> fail "design" "no design although 1 is not in the span"
      | Some l ->
          let tbl = E.H.create 16 in
          List.iter (fun (m, c) -> E.H.replace tbl m c) l;
          let value m = Option.value (E.H.find_opt tbl m) ~default:K3.zero in
          check "design is 1 on 1" (K3.is_one (value Mono.Word.one));
          check "design vanishes on generators" (Array.for_all (fun g -> K3.is_zero (R.apply value g)) gens)
  done

(* ------------------------------------------------------------------- LP *)
let test_lp () =
  let st = rng 5 in
  let certs = ref 0 and points = ref 0 in
  for _ = 1 to 300 do
    let nv = 1 + Random.State.int st 4 and k = 1 + Random.State.int st 8 in
    let rows =
      Array.init k (fun _ ->
          ( Array.of_list (List.filter_map (fun v -> let c = Random.State.int st 5 - 2 in if c = 0 then None else Some (v, Q.of_int c)) (List.init nv Fun.id)),
            Q.of_int (Random.State.int st 5 - 2) ))
    in
    let satisfied z = Array.for_all (fun (a, b) -> Q.geq (Array.fold_left (fun s (v, c) -> Q.add s (Q.mul c z.(v))) Q.zero a) b) rows in
    match Lp.farkas ~nvars:nv rows with
    | Lp.Certificate _ ->
        incr certs;
        (* Σ yᵢ(aᵢ·z − bᵢ) ≥ 0 at a solution z, but it equals −Σ yᵢbᵢ < 0: so no solution; spot-check *)
        let random_point () = Array.init nv (fun _ -> Q.of_ints (Random.State.int st 21 - 10) (1 + Random.State.int st 4)) in
        check "certificate means no solution" (not (List.exists satisfied (List.init 50 (fun _ -> random_point ()))))
    | Lp.Point z ->
        incr points;
        check "point satisfies all rows" (satisfied z)
    | Lp.Undecided e -> fail "farkas undecided" e
  done;
  check "both kinds of answers occur" (!certs > 20 && !points > 20);
  (* feasible y ≥ 0, A y = b by construction *)
  for _ = 1 to 200 do
    let m = 1 + Random.State.int st 5 and k = 1 + Random.State.int st 8 in
    let cols = Array.init k (fun _ -> Array.of_list (List.filter_map (fun i -> let c = Random.State.int st 7 - 3 in if c = 0 then None else Some (i, Q.of_int c)) (List.init m Fun.id))) in
    let y = Array.init k (fun _ -> Q.of_int (Random.State.int st 3)) in
    let rhs = Array.make m Q.zero in
    Array.iteri (fun j c -> Array.iter (fun (i, v) -> rhs.(i) <- Q.add rhs.(i) (Q.mul v y.(j))) c) cols;
    match Lp.nonneg ~m cols rhs with
    | Lp.Solution sol ->
        let acc = Array.make m Q.zero in
        List.iter (fun (j, v) -> Array.iter (fun (i, c) -> acc.(i) <- Q.add acc.(i) (Q.mul c v)) cols.(j)) sol;
        check "nonneg solution is exact" (Array.for_all2 Q.equal acc rhs && List.for_all (fun (_, v) -> Q.sign v >= 0) sol)
    | Lp.No_solution -> fail "nonneg" "feasible system reported infeasible"
    | Lp.Unknown e -> fail "nonneg" e
  done

(* ------------------------------------------------------------- dense / SDP *)
let test_dense () =
  let st = rng 6 in
  List.iter
    (fun n ->
      let a = Array.init n (fun _ -> Array.init n (fun _ -> Random.State.float st 2.0 -. 1.0)) in
      let s = Array.init n (fun i -> Array.init n (fun j -> a.(i).(j) +. a.(j).(i))) in
      let d, v = Dense.eigh s in
      let err = ref 0.0 in
      for k = 0 to n - 1 do
        for i = 0 to n - 1 do
          let sv = ref 0.0 in
          for j = 0 to n - 1 do
            sv := !sv +. (s.(i).(j) *. v.(j).(k))
          done;
          err := Float.max !err (Float.abs (!sv -. (d.(k) *. v.(i).(k))))
        done
      done;
      check (Printf.sprintf "eigh residual n=%d" n) (!err < 1e-10);
      check (Printf.sprintf "psd part n=%d" n) (Dense.min_eig (Dense.psd_part s) > -1e-10))
    [ 1; 2; 3; 10; 40 ];
  (* the SDP solver on a tiny Gram problem: x² ... find Q ⪰ 0 on (1, x) with
     Q11 = 1, 2·Q12 + Q22 = −1 (that is, 1 − x represented with x² = x) *)
  let p = { Sdp.nb = 2; m = 2; entry_row = [| [| 0; 1 |]; [| 0; 1 |] |]; hcols = [||]; c = [| 1.0; -1.0 |] } in
  match Sdp.solve p with
  | None -> fail "sdp" "no solution for a feasible Gram problem"
  | Some s ->
      check "sdp solution is PSD" (Dense.min_eig s.Sdp.q > -1e-9);
      check "sdp solution satisfies the equations" (Float.abs (s.Sdp.q.(0).(0) -. 1.0) < 1e-6 && Float.abs ((2.0 *. s.Sdp.q.(0).(1)) +. s.Sdp.q.(1).(1) +. 1.0) < 1e-6)

(* --------------------------------------------------------------- codecs *)
let test_json () =
  let b40 = Z.pow (Z.of_int 10) 40 in
  check "z roundtrip" (Json.roundtrip Json.z b40 = Ok b40);
  check "q roundtrip" (Json.roundtrip Json.q (Q.of_ints (-7) 12) = Ok (Q.of_ints (-7) 12));
  let m = Measures.(empty |> int "size" 3 |> big "c" b40 |> text "s" "x" |> flag "w" true) in
  check "measures roundtrip" (Result.map Measures.to_list (Json.roundtrip Measures.codec m) = Ok (Measures.to_list m));
  err "decode errors name the field" (Json.D.field "x" Json.D.int (`Assoc [ ("x", `String "no") ]))

let test_lang () =
  let st = rng 7 in
  for _ = 1 to 200 do
    let n = 1 + Random.State.int st 8 in
    let cls = List.init (Random.State.int st 10) (fun _ -> List.map (fun v -> if Random.State.bool st then v else -v) (random_set st n (1 + Random.State.int st 3))) in
    let c = Cnf.of_lists ~num_vars:n cls in
    match Cnf.of_dimacs (Cnf.to_dimacs c) with
    | Ok c' -> check "dimacs roundtrip" (Cnf.sha256 c = Cnf.sha256 c')
    | Error e -> fail "dimacs roundtrip" e
  done;
  (* content hashes are part of the database: they must never change *)
  let php32 = Families.php 2 in
  check "stable hash php-3-2" (Lang.problem_sha256 php32.problem = "1f7b275aebefd0fc4862ccd0fa6eebe189e42e73aac587e2b757368b80d5dfff");
  let t = Families.tseitin "grid" (Families.Two (3, 3)) in
  check "stable hash tseitin-grid-3x3" (Lang.problem_sha256 t.problem = "e7b2a6898cf52f706c0f47d1bf14f075897f1fc4dc51ee182a78d27ad5ca40f2");
  err "strict clause parsing" (Clause.of_list_strict [ 1; -1; 1 ])

let () =
  case "monomials" test_monomials;
  case "fields" test_fields;
  case "ring" test_ring;
  case "echelon" test_echelon;
  case "lp" test_lp;
  case "dense" test_dense;
  case "json" test_json;
  case "lang" test_lang;
  finish "algebra"
