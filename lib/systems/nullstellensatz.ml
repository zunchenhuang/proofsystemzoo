(* Nullstellensatz over GF(p): exact minimum-degree search, with designs as
   lower-bound certificates. Proof format ns/2:

     {"format": "ns/2", "p": p, "terms": [{"ax": i, "mult": [[[vars], c], ...]}, ...]}

   certifies Σᵢ gᵢ·fᵢ = 1 over GF(p) (multilinear), gᵢ = Σ c·∏vars. A
   lower-bound certificate {"metric": "degree", "value": d, "p": p,
   "design": [[[vars], c], ...]} is a linear functional L on monomials with
   L(1) = 1 that vanishes on every m·fᵢ of degree < d: then no refutation of
   degree < d exists. *)
open System

let format = "ns/2"

type term = { ax : int; mult : (int list * int) list }
type proof = { p : int; terms : term list }
type lower_bound = { degree : int; field : int; design : (int list * int) list }

let proof_codec : proof Json.codec =
  let open Json in
  let term = codec (fun t -> E.obj [ ("ax", `Int t.ax); ("mult", (Algebraic.terms_codec int).encode t.mult) ]) (fun j ->
    let* ax = D.field "ax" D.int j in
    let+ mult = D.field "mult" (Algebraic.terms_codec int).decode j in
    { ax; mult })
  in
  codec
    (fun pr -> E.obj [ ("format", `String format); ("p", `Int pr.p); ("terms", E.list term.encode pr.terms) ])
    (fun j ->
      let* () = D.tag "format" format j in
      let* p = D.field "p" D.int j in
      let+ terms = D.field "terms" (D.list term.decode) j in
      { p; terms })

let lower_bound_codec : lower_bound Json.codec =
  let open Json in
  codec
    (fun l ->
      E.obj [ ("metric", `String "degree"); ("value", `Int l.degree); ("p", `Int l.field); ("design", (Algebraic.terms_codec int).encode l.design) ])
    (fun j ->
      let* () = D.tag "metric" "degree" j in
      let* degree = D.field "value" D.int j in
      let* field = D.field "p" D.int j in
      let+ design = D.field "design" (Algebraic.terms_codec int).decode j in
      { degree; field; design })

exception Stop of string

module Algo (K : Algebraic.GF) (M : Mono.S) = struct
  module R = Ring.Make (K) (M)
  module E = Echelon.Make (R)

  let p = K.characteristic
  let of_poly (f : Poly.poly) = R.of_ints (Poly.terms f)
  let lower_bound dd l = { degree = dd + 1; field = p; design = List.map (fun (m, c) -> (M.to_list m, K.to_int c)) l }

  let setup (ps : Poly.t) =
    let fs = Array.map of_poly ps.polys in
    let free = Array.map (fun f -> Algebraic.free_vars ps.num_vars (R.absorbing f)) fs in
    (fs, Array.map Poly.degree ps.polys, free)

  let search (lim : Limits.t) (ps : Poly.t) =
    let n = ps.num_vars in
    let top = match lim.max_degree with None -> n | Some d -> min d n in
    let max_gens = Limits.size lim 60_000 and deadline = Limits.deadline lim in
    let fs, degs, free = setup ps in
    match Array.find_opt (fun i -> R.is_constant fs.(i)) (Array.init (Array.length fs) Fun.id) with
    | Some i ->
        refutation ~measures:Measures.(empty |> int "degree" 0 |> int "mult_terms" 1)
          { p; terms = [ { ax = i; mult = [ ([], K.to_int (K.inv (R.lead_coef fs.(i)))) ] } ] }
    | None -> (
        let ech = E.create () and gens = Vec.create (0, M.one) in
        let design = ref None and d = ref 0 in
        let lb () = Option.map (fun (dd, l) -> lower_bound dd l) !design in
        let stop msg = unknown ~measures:Measures.(empty |> int "degree_lb" !d) ?lower_bound:(lb ()) msg in
        let rec loop dd =
          if dd > top then
            if top = n then model ~measures:Measures.(empty |> int "generators" (Vec.length gens)) (Printf.sprintf "1 not in span at degree n=%d" n)
            else unknown ~measures:Measures.(empty |> int "degree_lb" (top + 1)) ?lower_bound:(lb ()) (Printf.sprintf "no refutation of degree <= %d" top)
          else begin
            d := dd;
            Array.iteri
              (fun i f ->
                let k = dd - degs.(i) in
                if k >= 0 && not (R.is_zero f) then
                  Seq.iter
                    (fun m ->
                      let m = M.of_list m in
                      let gid = Vec.push gens (i, m) in
                      if gid >= max_gens then raise (Stop (Printf.sprintf "more than %d generators at degree %d" max_gens dd));
                      ignore (E.add ech (R.mul_mono m f) ~gen:gid);
                      if gid land 511 = 0 then Clock.check deadline)
                    (Seqx.combinations free.(i) k))
              fs;
            match E.express ech R.one with
            | Some combo ->
                let by = Hashtbl.create 16 in
                List.iter
                  (fun (g, c) ->
                    let i, m = Vec.get gens g in
                    Hashtbl.replace by i ((M.to_list m, K.to_int c) :: Option.value (Hashtbl.find_opt by i) ~default:[]))
                  combo;
                let terms =
                  Hashtbl.fold (fun ax l acc -> { ax; mult = List.sort (fun (a, _) (b, _) -> Mono.compare_lists a b) l } :: acc) by []
                  |> List.sort (fun a b -> Int.compare a.ax b.ax)
                in
                let nterms = List.fold_left (fun s t -> s + List.length t.mult) 0 terms in
                refutation ?lower_bound:(lb ())
                  ~measures:Measures.(empty |> int "degree" dd |> int "mult_terms" nterms |> int "generators" (Vec.length gens) |> int "rank" (E.rank ech))
                  { p; terms }
            | None ->
                design := Option.map (fun l -> (dd, l)) (E.design ech);
                loop (dd + 1)
          end
        in
        try loop 1 with Stop s -> stop s | Clock.Timeout -> stop budget_message)

  let verify (ps : Poly.t) (pr : proof) =
    if pr.p <> p then Error "proof is over another field"
    else begin
      let fs = Array.map of_poly ps.polys in
      let acc = E.H.create 1024 and deg = ref 0 and nterms = ref 0 in
      let add m c = E.H.replace acc m (K.add c (Option.value (E.H.find_opt acc m) ~default:K.zero)) in
      let term k t =
        if t.ax < 0 || t.ax >= Array.length fs then Error (Printf.sprintf "term %d: no input polynomial %d" k t.ax)
        else
          Seqx.iter_result
            (fun (vs, c) ->
              if not (Algebraic.check_mono ps.num_vars vs) then Error (Printf.sprintf "term %d: malformed monomial" k)
              else begin
                let g = R.mul_mono (M.of_list vs) fs.(t.ax) and c = K.of_int c in
                Array.iteri (fun q m -> add m (K.mul c g.R.cs.(q))) g.R.ms;
                deg := max !deg (List.length vs + Poly.degree ps.polys.(t.ax));
                incr nterms;
                Ok ()
              end)
            (List.to_seq t.mult)
      in
      match Seqx.iter_result (fun (k, t) -> term k t) (List.to_seq (List.mapi (fun k t -> (k, t)) pr.terms)) with
      | Error e -> Error e
      | Ok () ->
          let residual = E.H.fold (fun m c l -> if K.is_zero c then l else (m, c) :: l) acc [] in
          if (match residual with [ (m, c) ] -> M.equal m M.one && K.is_one c | _ -> false) then
            Ok Measures.(empty |> int "degree" !deg |> int "mult_terms" !nterms)
          else Error (Printf.sprintf "Σ g·f ≠ 1 (residual has %d monomials)" (List.length residual))
    end

  let check_lower_bound (ps : Poly.t) (l : lower_bound) =
    if l.field <> p then Error "certificate is over another field"
    else begin
      let dd = l.degree - 1 in
      let h = E.H.create 1024 in
      let ok = ref (Ok ()) in
      List.iter
        (fun (vs, c) ->
          if not (Algebraic.check_mono ps.num_vars vs) then ok := Error "malformed monomial in design" else E.H.replace h (M.of_list vs) (K.of_int c))
        l.design;
      let value m = Option.value (E.H.find_opt h m) ~default:K.zero in
      match !ok with
      | Error e -> Error e
      | Ok () when not (K.is_one (value M.one)) -> Error "design does not take value 1 on the constant monomial"
      | Ok () -> (
          let fs, degs, free = setup ps in
          let violation = ref None in
          Array.iteri
            (fun i f ->
              if !violation = None && not (R.is_zero f) then
                Seq.iter
                  (fun m -> if !violation = None && not (K.is_zero (R.apply value (R.mul_mono (M.of_list m) f))) then violation := Some i)
                  (Seqx.subsets_upto free.(i) (dd - degs.(i))))
            fs;
          match !violation with
          | Some i -> Error (Printf.sprintf "design does not vanish on a multiple of f_%d" i)
          | None -> Ok Measures.(empty |> int "degree_lb_certified" (dd + 1)))
    end
end

(* the field is fixed by the parameters, the monomial representation by the
   instance: both are chosen at run time and the algorithm is instantiated
   for exactly that pair *)
module type CORE = sig
  val p : int
  val search : Limits.t -> Poly.t -> (proof, lower_bound) outcome
  val verify : Poly.t -> proof -> (Measures.t, string) result
  val check_lower_bound : Poly.t -> lower_bound -> (Measures.t, string) result
end

module Core (K : Algebraic.GF) : CORE = struct
  let p = K.characteristic

  let search lim (ps : Poly.t) =
    let (module M) = Mono.for_vars ps.num_vars in
    let module A = Algo (K) (M) in
    A.search lim ps

  let verify (ps : Poly.t) pr =
    let (module M) = Mono.for_vars ps.num_vars in
    let module A = Algo (K) (M) in
    A.verify ps pr

  let check_lower_bound (ps : Poly.t) l =
    let (module M) = Mono.for_vars ps.num_vars in
    let module A = Algo (K) (M) in
    A.check_lower_bound ps l
end

type config = (module CORE)
type input = Poly.t

let name = "nullstellensatz"
let version = "0.3"

let info =
  {
    group = "algebraic";
    order = 0;
    line_type = "polynomial";
    primary_metric = "degree";
    book = "6.2";
    simulates = [];
    description = "Nullstellensatz over GF(p); exact minimum-degree search, designs as lower bounds";
  }

let language = Lang.Poly
let encoding = Some "cnf-poly"
let params = [ Algebraic.p_param ]
let variants = [ [ ("p", "2") ]; [ ("p", "3") ] ]
let label env = "NS" ^ Param.get env "p"

let configure env =
  let (module K) = Algebraic.field_of_env env in
  Ok (module Core (K) : CORE)

let searches _ = true
let search ((module C) : config) lim ps = C.search lim ps
let proof = proof_codec
let lower_bound = lower_bound_codec
let verify ((module C) : config) ps pr = C.verify ps pr
let check_lower_bound ((module C) : config) ps l = C.check_lower_bound ps l
let parse_text = None
