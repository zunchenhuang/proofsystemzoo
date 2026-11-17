(* Sum-of-Squares over ℚ. Proof format sos/1:

     {"format": "sos/1",
      "squares": [{"c": "q", "s": [[[vars], "q"], ...]}, ...],
      "ideal":   [{"ax": i, "mult": [[[vars], "q"], ...]}, ...]}

   certifies Σ c·s² + Σ hᵢ·fᵢ = −1 (multilinear, c ≥ 0), which no 0/1 root
   of the fᵢ can satisfy. The degree is the largest of 2·deg s and
   deg hᵢ + deg fᵢ.

   cone=dsos restricts the squares to x^a and (x^a ± x^b)² — diagonally
   dominant Gram matrices — and is searched by the certified LP.
   cone=sos allows any squares and is searched by a semidefinite program
   whose numerical solution is rounded to an exact Gram matrix and
   decomposed into squares (see {!Sdp}). *)
open System

let format = "sos/1"

type qpoly = (int list * Q.t) list
type square = { c : Q.t; s : qpoly }
type ideal_term = { ax : int; mult : qpoly }
type proof = { squares : square list; ideal : ideal_term list }

let qpoly_codec = Algebraic.terms_codec Json.q

let codec : proof Json.codec =
  let open Json in
  let square =
    codec
      (fun sq -> E.obj [ ("c", E.q sq.c); ("s", qpoly_codec.encode sq.s) ])
      (fun j ->
        let* c = D.field "c" D.q j in
        let+ s = D.field "s" qpoly_codec.decode j in
        { c; s })
  in
  let ideal =
    codec
      (fun t -> E.obj [ ("ax", `Int t.ax); ("mult", qpoly_codec.encode t.mult) ])
      (fun j ->
        let* ax = D.field "ax" D.int j in
        let+ mult = D.field "mult" qpoly_codec.decode j in
        { ax; mult })
  in
  codec
    (fun pr -> E.obj [ ("format", `String format); ("squares", E.list square.encode pr.squares); ("ideal", E.list ideal.encode pr.ideal) ])
    (fun j ->
      let* () = D.tag "format" format j in
      let* squares = D.field "squares" (D.list square.decode) j in
      let+ ideal = D.field "ideal" (D.list ideal.decode) j in
      { squares; ideal })

type cone = Sos | Dsos

module Algo (M : Mono.S) = struct
  module R = Ring.Make (Field.Rational) (M)

  module H = Hashtbl.Make (struct
    type t = M.t

    let equal = M.equal
    let hash = M.hash
  end)

  let of_poly (f : Poly.poly) = R.of_ints (Poly.terms f)
  let of_q (p : qpoly) = R.of_terms (List.map (fun (vs, c) -> (M.of_list vs, c)) p)
  let to_q (p : R.t) : qpoly = List.rev_map (fun (m, c) -> (M.to_list m, c)) (R.terms p)

  let verify cone (ps : Poly.t) (pr : proof) =
    let n = ps.num_vars in
    let in_range p = List.for_all (fun (vs, _) -> Algebraic.check_mono n vs) p in
    let acc = H.create 1024 in
    let add (p : R.t) c = Array.iteri (fun q m -> H.replace acc m (Q.add (Q.mul c p.R.cs.(q)) (Option.value (H.find_opt acc m) ~default:Q.zero))) p.R.ms in
    (* c·s²: s = s'/D with integer s', so s'² is expanded in ℤ (no gcd per
       product) and scaled once per monomial *)
    let add_square c (s : R.t) =
      let d = Array.fold_left (fun l q -> Z.lcm l (Q.den q)) Z.one s.R.cs in
      let zs = Array.map (fun q -> Z.mul (Q.num q) (Z.divexact d (Q.den q))) s.R.cs in
      let local = H.create (4 * R.size s) in
      let n = R.size s in
      for i = 0 to n - 1 do
        for j = i to n - 1 do
          let m = M.mul s.R.ms.(i) s.R.ms.(j) in
          let v = Z.mul zs.(i) zs.(j) in
          let v = if i = j then v else Z.shift_left v 1 in
          H.replace local m (Z.add v (Option.value (H.find_opt local m) ~default:Z.zero))
        done
      done;
      let f = Q.div c (Q.of_bigint (Z.mul d d)) in
      H.iter (fun m v -> if Z.sign v <> 0 then H.replace acc m (Q.add (Q.mul f (Q.of_bigint v)) (Option.value (H.find_opt acc m) ~default:Q.zero))) local
    in
    let deg = ref 0 and size = ref 0 in
    let square k sq =
      if Q.sign sq.c < 0 then Error (Printf.sprintf "square %d: negative weight" k)
      else if not (in_range sq.s) then Error (Printf.sprintf "square %d: malformed monomial" k)
      else begin
        let s = of_q sq.s in
        let shape_ok =
          cone = Sos
          ||
          match s.R.cs with [| v |] -> Q.equal v Q.one | [| a; b |] -> Q.equal (Q.abs a) Q.one && Q.equal (Q.abs b) Q.one | _ -> false
        in
        if not shape_ok then Error (Printf.sprintf "square %d: not of the form x^a or x^a ± x^b" k)
        else begin
          add_square sq.c s;
          deg := max !deg (2 * R.degree s);
          size := !size + R.size s;
          Ok ()
        end
      end
    in
    let ideal k t =
      if t.ax < 0 || t.ax >= Array.length ps.polys then Error (Printf.sprintf "ideal term %d: no input polynomial %d" k t.ax)
      else if not (in_range t.mult) then Error (Printf.sprintf "ideal term %d: malformed monomial" k)
      else begin
        let h = of_q t.mult in
        add (R.mul h (of_poly ps.polys.(t.ax))) Q.one;
        deg := max !deg (R.degree h + Poly.degree ps.polys.(t.ax));
        size := !size + R.size h;
        Ok ()
      end
    in
    let ( let* ) = Result.bind in
    let* () = Seqx.iter_result (fun (k, sq) -> square k sq) (List.to_seq (List.mapi (fun k x -> (k, x)) pr.squares)) in
    let* () = Seqx.iter_result (fun (k, t) -> ideal k t) (List.to_seq (List.mapi (fun k x -> (k, x)) pr.ideal)) in
    match H.fold (fun m c l -> if Q.sign c = 0 then l else (m, c) :: l) acc [] with
    | [ (m, c) ] when M.equal m M.one && Q.equal c Q.minus_one ->
        Ok Measures.(empty |> int "degree" !deg |> int "squares" (List.length pr.squares) |> int "size" !size)
    | residual -> Error (Printf.sprintf "Σ c·s² + Σ h·f ≠ −1 (residual has %d monomials)" (List.length residual))

  (* monomials of degree ≤ k, by degree *)
  let monomials n k = List.concat_map (fun size -> List.of_seq (Seqx.combinations (Array.init n (fun i -> i + 1)) size)) (List.init (k + 1) Fun.id)

  (* the multipliers m·fᵢ with deg m + deg fᵢ ≤ d (non-absorbing m) *)
  let generators (ps : Poly.t) d =
    List.concat
      (List.mapi
         (fun i (f0 : Poly.poly) ->
           let f = of_poly f0 in
           let k = d - Poly.degree f0 in
           if k < 0 || R.is_zero f then []
           else
             let free = Algebraic.free_vars ps.num_vars (R.absorbing f) in
             List.of_seq (Seq.map (fun m -> (i, m, R.mul_mono (M.of_list m) f)) (Seqx.subsets_upto free k)))
         (Array.to_list ps.polys))

  (* group ideal coefficients by axiom *)
  let ideal_of (contribs : (int * int list * Q.t) list) =
    let by = Hashtbl.create 16 in
    List.iter (fun (i, m, c) -> Hashtbl.replace by i ((M.of_list m, c) :: Option.value (Hashtbl.find_opt by i) ~default:[])) contribs;
    Hashtbl.fold (fun ax l acc -> let p = R.of_terms l in if R.is_zero p then acc else { ax; mult = to_q p } :: acc) by []
    |> List.sort (fun a b -> Int.compare a.ax b.ax)

  let dsos (lim : Limits.t) (ps : Poly.t) =
    let n = ps.num_vars in
    let top = let c = n + (n mod 2) in match lim.max_degree with None -> c | Some d -> min d c in
    let max_cols = Limits.size lim 60_000 and deadline = Limits.deadline lim in
    let tried d = Measures.(empty |> int "degree_tried" d) in
    let rec loop d last =
      if d > top then unknown ~measures:(tried last) (Printf.sprintf "no DSOS refutation found up to degree %d (not certified)" top)
      else begin
        let basis = Array.of_list (List.map M.of_list (monomials n (d / 2))) in
        let gens = generators ps d in
        let nb = Array.length basis in
        if (nb * (nb + 1)) + (2 * List.length gens) > max_cols then unknown ~measures:(tried last) (Printf.sprintf "DSOS LP too large at degree %d" d)
        else begin
          let ids = H.create 1024 in
          let id m = match H.find_opt ids m with Some i -> i | None -> let i = H.length ids in H.replace ids m i; i in
          let cols = Vec.create [||] and meta = Vec.create (`Sq R.zero) in
          let col (p : R.t) = Array.mapi (fun q m -> (id m, p.R.cs.(q))) p.R.ms in
          let push c x = ignore (Vec.push cols c); ignore (Vec.push meta x) in
          Array.iter (fun b -> let s = R.monomial b Q.one in push (col s) (`Sq s)) basis;
          for x = 0 to nb - 1 do
            for y = x + 1 to nb - 1 do
              List.iter
                (fun sg ->
                  let s = R.add (R.monomial basis.(x) Q.one) (R.monomial basis.(y) sg) in
                  push (col (R.mul s s)) (`Sq s))
                [ Q.one; Q.minus_one ]
            done
          done;
          List.iter (fun (i, m, g) -> List.iter (fun sg -> push (col (R.scale sg g)) (`Id (i, m, sg))) [ Q.one; Q.minus_one ]) gens;
          let const = id M.one in
          let m = H.length ids in
          let rhs = Array.init m (fun i -> if i = const then Q.minus_one else Q.zero) in
          match Lp.nonneg ~deadline ~m (Vec.to_array cols) rhs with
          | Lp.Solution y ->
              let squares = ref [] and contribs = ref [] in
              List.iter
                (fun (j, v) ->
                  match Vec.get meta j with
                  | `Sq s -> squares := { c = v; s = to_q s } :: !squares
                  | `Id (i, mono, sg) -> contribs := (i, mono, Q.mul sg v) :: !contribs)
                y;
              let pr = { squares = List.rev !squares; ideal = ideal_of !contribs } in
              ( match verify Dsos ps pr with
              | Ok ms -> refutation ~measures:ms pr
              | Error e -> unknown ("internal: certificate rejected: " ^ e) )
          | Lp.No_solution | Lp.Unknown _ -> loop (d + 2) d
        end
      end
    in
    try loop 2 0 with Clock.Timeout -> unknown budget_message

  (* ---------------------------------------------- cone = sos, by SDP *)

  (* Σ_S χ_S² over |S| ≤ k, χ_S = ∏_{i∈S}(1 − 2xᵢ), is the constant N (each
     χ_S² = 1 on the cube) and its Gram matrix in the monomial basis is
     CᵀC for the invertible change of basis C: positive definite. Entry
     (a, b) is (−2)^{|a|+|b|}·#{S : |S| ≤ k, S ⊇ a ∪ b}. *)
  let fourier_gram n k (basis : int list array) =
    let rec binom n r = if r < 0 || r > n then Z.zero else if r = 0 then Z.one else Z.div (Z.mul (binom (n - 1) (r - 1)) (Z.of_int n)) (Z.of_int r) in
    let count u = List.fold_left Z.add Z.zero (List.init (max 0 (k - u + 1)) (fun j -> binom (n - u) j)) in
    let counts = Array.init (2 * k + 1) count in
    Array.map
      (fun a ->
        Array.map
          (fun b ->
            let u = List.length (List.sort_uniq compare (a @ b)) in
            let sign = if (List.length a + List.length b) mod 2 = 0 then Z.one else Z.minus_one in
            Z.mul sign (Z.mul (Z.shift_left Z.one (List.length a + List.length b)) counts.(u)))
          basis)
      basis

  (* exact L·D·Lᵀ of a symmetric rational matrix; None unless it is PSD *)
  let ldl (q : Q.t array array) =
    let n = Array.length q in
    let a = Array.map Array.copy q and d = Array.make n Q.zero in
    let l = Array.init n (fun i -> Array.init n (fun j -> if i = j then Q.one else Q.zero)) in
    let ok = ref true in
    for k = 0 to n - 1 do
      if !ok then begin
        let p = a.(k).(k) in
        if Q.sign p < 0 then ok := false
        else if Q.sign p = 0 then (for i = k + 1 to n - 1 do if Q.sign a.(i).(k) <> 0 then ok := false done)
        else begin
          d.(k) <- p;
          for i = k + 1 to n - 1 do
            l.(i).(k) <- Q.div a.(i).(k) p
          done;
          for i = k + 1 to n - 1 do
            let lik = l.(i).(k) in
            if Q.sign lik <> 0 then
              for j = k + 1 to i do
                a.(i).(j) <- Q.sub a.(i).(j) (Q.mul lik a.(j).(k))
              done
          done;
          for i = k + 1 to n - 1 do
            for j = k + 1 to i do
              a.(j).(i) <- a.(i).(j)
            done
          done
        end
      end
    done;
    if !ok then Some (d, l) else None

  let dyadic bits (x : float) = Q.make (Z.of_float (Float.round (Float.ldexp x bits))) (Z.shift_left Z.one bits)

  (* Round the numerical solution (target −2) to an exact certificate:
     round the multipliers, add the Fourier Gram matrix scaled to represent
     +1 (this gives target −1 and a positive-definite margin), project the
     Gram matrix exactly onto the coefficient equations (each monomial's
     entries move by the same amount), and decompose it by exact LDLᵀ. *)
  let certify_at bits (ps : Poly.t) (basis : int list array) (bm : M.t array) gens (sol : Sdp.solution) =
    let n = ps.num_vars and nb = Array.length basis in
    let k = List.fold_left (fun m b -> max m (List.length b)) 0 (Array.to_list basis) in
    let hq = Array.map (dyadic bits) sol.Sdp.h in
    let target = H.create 256 in
    let addt m v = H.replace target m (Q.add v (Option.value (H.find_opt target m) ~default:Q.zero)) in
    addt M.one Q.minus_one;
    List.iteri (fun j (_, _, (g : R.t)) -> if Q.sign hq.(j) <> 0 then Array.iteri (fun q mono -> addt mono (Q.neg (Q.mul hq.(j) g.R.cs.(q)))) g.R.ms) gens;
    let g = fourier_gram n k basis in
    let nq = Q.of_int nb in
    let q = Array.init nb (fun a -> Array.init nb (fun b -> if b < a then Q.zero else Q.add (dyadic bits sol.Sdp.q.(a).(b)) (Q.div (Q.of_bigint g.(a).(b)) nq))) in
    let groups = H.create 256 in
    for a = 0 to nb - 1 do
      for b = a to nb - 1 do
        let mu = M.mul bm.(a) bm.(b) in
        H.replace groups mu ((a, b) :: Option.value (H.find_opt groups mu) ~default:[])
      done
    done;
    let consistent = ref true in
    H.iter (fun mu _ -> if not (H.mem groups mu) then consistent := false) target;
    H.iter
      (fun mu entries ->
        let w (a, b) = if a = b then Q.one else Q.of_int 2 in
        let cur = List.fold_left (fun s (a, b) -> Q.add s (Q.mul (w (a, b)) q.(a).(b))) Q.zero entries in
        let size = List.fold_left (fun s e -> Q.add s (w e)) Q.zero entries in
        let delta = Q.div (Q.sub (Option.value (H.find_opt target mu) ~default:Q.zero) cur) size in
        if Q.sign delta <> 0 then List.iter (fun (a, b) -> q.(a).(b) <- Q.add q.(a).(b) delta) entries)
      groups;
    for a = 0 to nb - 1 do
      for b = 0 to a - 1 do
        q.(a).(b) <- q.(b).(a)
      done
    done;
    if not !consistent then None
    else
      match ldl q with
      | None -> None
      | Some (d, l) ->
          let squares =
            List.filter_map
              (fun kk ->
                if Q.sign d.(kk) = 0 then None
                else
                  Some { c = d.(kk); s = List.filter_map (fun i -> if Q.sign l.(i).(kk) = 0 then None else Some (basis.(i), l.(i).(kk))) (List.init nb Fun.id) })
              (List.init nb Fun.id)
          in
          let contribs = List.concat (List.mapi (fun j (i, m, _) -> if Q.sign hq.(j) = 0 then [] else [ (i, m, hq.(j)) ]) gens) in
          Some { squares; ideal = ideal_of contribs }

  (* the coarsest rounding that still gives a positive semidefinite Gram
     matrix: coefficients stay short, so the exact LDLᵀ and the verifier
     stay fast *)
  let certify ps basis bm gens sol = List.find_map (fun bits -> certify_at bits ps basis bm gens sol) [ 8; 12; 16; 20; 26; 32; 40 ]

  let sos (lim : Limits.t) (ps : Poly.t) =
    let n = ps.num_vars in
    let top = let c = n + (n mod 2) in match lim.max_degree with None -> c | Some d -> min d c in
    let max_basis = Limits.size lim 120 and deadline = Limits.deadline lim in
    let tried d = Measures.(empty |> int "degree_tried" d) in
    let rec loop d last =
      if d > top then unknown ~measures:(tried last) (Printf.sprintf "no SoS refutation found up to degree %d (not certified)" top)
      else begin
        let basis = Array.of_list (monomials n (d / 2)) in
        let nb = Array.length basis in
        if nb > max_basis then unknown ~measures:(tried last) (Printf.sprintf "Gram basis of %d monomials at degree %d > max_size=%d" nb d max_basis)
        else begin
          let bm = Array.map M.of_list basis in
          let gens = generators ps d in
          let ids = H.create 1024 in
          let id m = match H.find_opt ids m with Some i -> i | None -> let i = H.length ids in H.replace ids m i; i in
          let entry_row = Array.init nb (fun a -> Array.init nb (fun b -> if b >= a then id (M.mul bm.(a) bm.(b)) else 0)) in
          let hcols = Array.of_list (List.map (fun (_, _, (g : R.t)) -> Array.mapi (fun q mono -> (id mono, Q.to_float g.R.cs.(q))) g.R.ms) gens) in
          let const = id M.one in
          let m = H.length ids in
          let c = Array.init m (fun i -> if i = const then -2.0 else 0.0) in
          (* a degree gets at most half of the time that is left *)
          let share = Option.map (fun r -> Clock.now () +. (r /. 2.0)) (Clock.remaining deadline) in
          let sol, t_sdp = Clock.time (fun () -> Sdp.solve ~deadline:share { Sdp.nb; m; entry_row; hcols; c }) in
          if Lp.debug then Printf.eprintf "[sos] d=%d nb=%d m=%d gens=%d: sdp %s in %.2fs\n%!" d nb m (List.length gens) (match sol with Some s -> Printf.sprintf "converged (%d it, gap %.1e)" s.Sdp.iterations s.Sdp.residual | None -> "failed") t_sdp;
          match sol with
          | None -> loop (d + 2) d
          | Some sol -> (
              let cert, t_cert = Clock.time (fun () -> certify ps basis bm gens sol) in
              if Lp.debug then Printf.eprintf "[sos]   certify %s in %.2fs\n%!" (if cert = None then "failed" else "ok") t_cert;
              match cert with
              | None -> loop (d + 2) d
              | Some pr ->
                  (* exact LDLᵀ succeeded, so this is a certificate by
                     construction; the runner verifies it independently *)
                  refutation ~measures:Measures.(empty |> int "sdp_iterations" sol.Sdp.iterations |> int "degree_bound" d) pr)
        end
      end
    in
    try loop 2 0 with Clock.Timeout -> unknown budget_message

  let search cone lim ps = match cone with Dsos -> dsos lim ps | Sos -> sos lim ps

end

module type ALGO = sig
  val search : cone -> Limits.t -> Poly.t -> (proof, Nothing.t) outcome
  val verify : cone -> Poly.t -> proof -> (Measures.t, string) result
end

let with_algo (ps : Poly.t) f =
  let (module M) = Mono.for_vars ps.num_vars in
  f (module Algo (M) : ALGO)

type config = cone
type input = Poly.t
type lower_bound = Nothing.t

let name = "sum-of-squares"
let version = "0.3"

let info =
  {
    group = "semialgebraic";
    order = 2;
    line_type = "sum of squares + ideal";
    primary_metric = "degree";
    book = "6.4";
    simulates = [];
    description = "Sum-of-Squares over ℚ; cone=sos by rounded SDP, cone=dsos by certified LP";
  }

let language = Lang.Poly
let encoding = Some "cnf-poly"
let params = [ Param.choice ~key:"cone" ~default:"sos" [ "sos"; "dsos" ] ]
let variants = [ [ ("cone", "sos") ]; [ ("cone", "dsos") ] ]
let label env = String.uppercase_ascii (Param.get env "cone")
let configure env = match Param.get env "cone" with "dsos" -> Ok Dsos | _ -> Ok Sos
let searches _ = true
let search cone lim ps = with_algo ps (fun (module A) -> A.search cone lim ps)
let proof = codec
let lower_bound = Nothing.codec
let verify cone ps pr = with_algo ps (fun (module A) -> A.verify cone ps pr)
let check_lower_bound = Nothing.check
let parse_text = None
