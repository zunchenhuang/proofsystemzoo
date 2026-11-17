(* Cutting Planes: gcd rounding + clique cuts + exact LP, with a Resolution
   simulation as the fallback for clausal inputs. Proof format cp/1:

     {"format": "cp/1", "lines": [
        {"rule": "axiom", "ax": i}
      | {"rule": "bound", "var": v, "side": "lo" | "hi"}     x ≥ 0  |  −x ≥ −1
      | {"rule": "add", "from": [[j, c], ...]}              Σ c·line j, c > 0
      | {"rule": "div", "from": j, "d": d}                  divide by d, round up
     ]}

   ending in 0 ≥ b with b > 0. Coefficients are arbitrary-precision. *)
open System
module IM = Map.Make (Int)

let format = "cp/1"

type side = Lo | Hi
type line = Axiom of int | Bound of int * side | Add of (int * Z.t) list | Div of int * Z.t
type proof = line array

(* Σ a·x ≥ b *)
type value = { a : Z.t IM.t; b : Z.t }

let line_codec : line Json.codec =
  let open Json in
  let encode = function
    | Axiom i -> E.obj [ ("rule", `String "axiom"); ("ax", `Int i) ]
    | Bound (v, s) -> E.obj [ ("rule", `String "bound"); ("var", `Int v); ("side", `String (if s = Lo then "lo" else "hi")) ]
    | Add from -> E.obj [ ("rule", `String "add"); ("from", E.list (fun (j, c) -> `List [ `Int j; E.z c ]) from) ]
    | Div (j, d) -> E.obj [ ("rule", `String "div"); ("from", `Int j); ("d", E.z d) ]
  in
  let decode j =
    let* rule = rule_of j in
    match rule with
    | "axiom" -> Result.map (fun i -> Axiom i) (D.field "ax" D.int j)
    | "bound" -> (
        let* v = D.field "var" D.int j in
        let* s = D.field "side" D.string j in
        match s with "lo" -> Ok (Bound (v, Lo)) | "hi" -> Ok (Bound (v, Hi)) | s -> error "bad side %S" s)
    | "add" -> Result.map (fun l -> Add l) (D.field "from" (D.list (D.pair D.int D.z)) j)
    | "div" ->
        let* from = D.field "from" D.int j in
        let+ d = D.field "d" D.z j in
        Div (from, d)
    | r -> error "unknown rule %S" r
  in
  codec encode decode

let codec : proof Json.codec =
  let open Json in
  codec
    (fun lines -> E.obj [ ("format", `String format); ("lines", E.array line_codec.encode lines) ])
    (fun j ->
      let* () = D.tag "format" format j in
      D.field "lines" (D.array line_codec.decode) j)

let of_ineq (q : Ineq.ineq) = { a = List.fold_left (fun m (v, c) -> IM.add v (Z.of_int c) m) IM.empty q.terms; b = Z.of_int q.rhs }
let bound_value v = function Lo -> { a = IM.singleton v Z.one; b = Z.zero } | Hi -> { a = IM.singleton v Z.minus_one; b = Z.minus_one }

let combine (pairs : (value * Z.t) list) =
  let a, b =
    List.fold_left
      (fun (a, b) (v, c) -> (IM.union (fun _ x y -> Some (Z.add x y)) a (IM.map (Z.mul c) v.a), Z.add b (Z.mul c v.b)))
      (IM.empty, Z.zero) pairs
  in
  { a = IM.filter (fun _ x -> Z.sign x <> 0) a; b }

let divide v d = { a = IM.map (fun x -> Z.div x d) v.a; b = Z.cdiv v.b d }
let contradiction v = IM.is_empty v.a && Z.sign v.b > 0

(* ------------------------------------------------------------ checker *)

(* every line's value and rank (number of nested divisions) *)
let values (sys : Ineq.t) (lines : proof) : (value array * int array, string) result =
  let n = Array.length lines in
  let vals = Array.make n { a = IM.empty; b = Z.zero } and rank = Array.make n 0 in
  let line k =
    let earlier j = j >= 0 && j < k in
    let ( let* ) = Result.bind in
    let* v, r =
      match lines.(k) with
      | Axiom i ->
          if i < 0 || i >= Array.length sys.ineqs then Error (Printf.sprintf "line %d: no input inequality %d" k i) else Ok (of_ineq sys.ineqs.(i), 0)
      | Bound (v, s) -> if v < 1 || v > sys.num_vars then Error (Printf.sprintf "line %d: bad bound axiom" k) else Ok (bound_value v s, 0)
      | Add [] -> Error (Printf.sprintf "line %d: empty addition" k)
      | Add from ->
          if List.exists (fun (j, c) -> (not (earlier j)) || Z.sign c <= 0) from then
            Error (Printf.sprintf "line %d: addition needs earlier lines and positive coefficients" k)
          else Ok (combine (List.map (fun (j, c) -> (vals.(j), c)) from), List.fold_left (fun r (j, _) -> max r rank.(j)) 0 from)
      | Div (j, d) ->
          if (not (earlier j)) || Z.sign d <= 0 then Error (Printf.sprintf "line %d: bad division" k)
          else if IM.exists (fun _ x -> Z.sign (Z.rem x d) <> 0) vals.(j).a then
            Error (Printf.sprintf "line %d: %s does not divide every coefficient" k (Z.to_string d))
          else Ok (divide vals.(j) d, rank.(j) + 1)
    in
    vals.(k) <- v;
    rank.(k) <- r;
    Ok ()
  in
  Result.map (fun () -> (vals, rank)) (Seqx.iter_result line (Seqx.range 0 n))

let measures (vals, rank) (lines : proof) =
  let mx = Array.fold_left (fun m v -> IM.fold (fun _ x m -> Z.max m (Z.abs x)) v.a (Z.max m (Z.abs v.b))) Z.zero vals in
  Measures.(
    empty
    |> int "size" (Array.length lines)
    |> int "rank" rank.(Array.length rank - 1)
    |> int "divisions" (Array.fold_left (fun s l -> match l with Div _ -> s + 1 | _ -> s) 0 lines)
    |> big "max_coef" mx)

let check (sys : Ineq.t) (lines : proof) =
  if Array.length lines = 0 then Error "no lines"
  else
    match values sys lines with
    | Error e -> Error e
    | Ok (vals, rank) ->
        if not (contradiction vals.(Array.length vals - 1)) then Error "last line is not 0 ≥ b with b > 0" else Ok (measures (vals, rank) lines)

(* ------------------------------------------------------------ search *)

(* derivations are built in a scratch buffer, then the ancestors of the
   final line are renumbered into the proof *)
type builder = { sys : Ineq.t; lines : line Vec.t; vals : value Vec.t; bounds : (int * side, int) Hashtbl.t; axioms : (int, int) Hashtbl.t }

let push bd l v =
  ignore (Vec.push bd.vals v);
  Vec.push bd.lines l

let axiom bd i =
  match Hashtbl.find_opt bd.axioms i with
  | Some l -> l
  | None ->
      let l = push bd (Axiom i) (of_ineq bd.sys.ineqs.(i)) in
      Hashtbl.replace bd.axioms i l;
      l

let bound bd v side =
  match Hashtbl.find_opt bd.bounds (v, side) with
  | Some l -> l
  | None ->
      let l = push bd (Bound (v, side)) (bound_value v side) in
      Hashtbl.replace bd.bounds (v, side) l;
      l

let add bd pairs =
  match List.filter (fun (_, c) -> Z.sign c <> 0) pairs with
  | [ (l, c) ] when Z.equal c Z.one -> l
  | pairs -> push bd (Add pairs) (combine (List.map (fun (l, c) -> (Vec.get bd.vals l, c)) pairs))

let div bd l d = if Z.equal d Z.one then l else push bd (Div (l, d)) (divide (Vec.get bd.vals l) d)

let finish bd root : proof =
  let need = Hashtbl.create 64 and stack = ref [ root ] in
  while !stack <> [] do
    let k = List.hd !stack in
    stack := List.tl !stack;
    if not (Hashtbl.mem need k) then begin
      Hashtbl.replace need k ();
      match Vec.get bd.lines k with Add from -> stack := List.map fst from @ !stack | Div (j, _) -> stack := j :: !stack | _ -> ()
    end
  done;
  let order = List.sort compare (Hashtbl.fold (fun k () acc -> k :: acc) need []) in
  let ren = Hashtbl.create 64 in
  List.iteri (fun i o -> Hashtbl.replace ren o i) order;
  let r = Hashtbl.find ren in
  Array.of_list
    (List.map (fun o -> match Vec.get bd.lines o with Add from -> Add (List.map (fun (j, c) -> (r j, c)) from) | Div (j, d) -> Div (r j, d) | l -> l) order)

(* a Farkas combination of the given lines, if the LP finds one *)
(* the number of lines a row costs: itself and everything it is derived from *)
let cost bd r =
  let seen = Hashtbl.create 16 and stack = ref [ r ] in
  while !stack <> [] do
    let k = List.hd !stack in
    stack := List.tl !stack;
    if not (Hashtbl.mem seen k) then begin
      Hashtbl.replace seen k ();
      match Vec.get bd.lines k with Add from -> stack := List.map fst from @ !stack | Div (j, _) -> stack := j :: !stack | _ -> ()
    end
  done;
  Hashtbl.length seen

(* A Farkas combination of the given lines, if the LP finds one. Its rows
   are then economised: the most expensive rows of the support are excluded
   one at a time, keeping each exclusion after which the system is still
   infeasible (cheaper rows take their place), and finally every row the
   remaining support does not need is dropped. *)
let lp bd rows deadline =
  let rows = Array.of_list rows in
  let qrow r =
    let v = Vec.get bd.vals r in
    (Array.of_list (List.map (fun (x, c) -> (x - 1, Q.of_bigint c)) (IM.bindings v.a)), Q.of_bigint v.b)
  in
  let qrows = Array.map qrow rows in
  let solve (idx : int list) =
    let idx = Array.of_list idx in
    match Lp.farkas ~deadline ~nvars:bd.sys.num_vars (Array.map (fun i -> qrows.(i)) idx) with
    | Lp.Certificate y -> Some (List.filter_map (fun k -> if Q.sign y.(k) > 0 then Some (idx.(k), y.(k)) else None) (List.init (Array.length idx) Fun.id))
    | Lp.Point _ | Lp.Undecided _ -> None
  in
  let all = List.init (Array.length rows) Fun.id in
  match solve all with
  | None -> None
  | Some cert ->
      let cert = ref cert and excluded = ref [] and tried = Hashtbl.create 16 in
      let costs = Array.map (cost bd) rows in
      let by_cost l = List.sort (fun a b -> compare (costs.(b), b) (costs.(a), a)) l in
      let rec exclude () =
        match List.find_opt (fun j -> not (Hashtbl.mem tried j)) (by_cost (List.map fst !cert)) with
        | Some j when List.length all <= 400 && not (Clock.expired deadline) ->
            Hashtbl.replace tried j ();
            (match solve (List.filter (fun i -> not (List.mem i (j :: !excluded))) all) with
            | Some c ->
                excluded := j :: !excluded;
                cert := c
            | None -> ());
            exclude ()
        | _ -> ()
      in
      exclude ();
      List.iter
        (fun j ->
          if List.mem_assoc j !cert && List.length !cert > 1 && not (Clock.expired deadline) then
            match solve (List.filter (( <> ) j) (List.map fst !cert)) with Some c -> cert := c | None -> ())
        (by_cost (List.map fst !cert));
      let support = List.sort compare !cert in
      let c = Num.integral (Array.of_list (List.map snd support)) in
      Some (add bd (List.mapi (fun k (i, _) -> (rows.(i), c.(k))) support))

(* greedy maximal cliques in the graph of pairwise exclusions −x−y ≥ −1 *)
let cliques bd rows max_vars =
  let pair = Hashtbl.create 64 in
  List.iter
    (fun r ->
      let v = Vec.get bd.vals r in
      match IM.bindings v.a with
      | [ (u, cu); (w, cw) ] when Z.equal v.b Z.minus_one && Z.equal cu Z.minus_one && Z.equal cw Z.minus_one -> Hashtbl.replace pair (u, w) r
      | _ -> ())
    rows;
  let adj = Hashtbl.create 64 in
  let neighbours u = Option.value (Hashtbl.find_opt adj u) ~default:[] in
  Hashtbl.iter
    (fun (u, v) _ ->
      Hashtbl.replace adj u (v :: neighbours u);
      Hashtbl.replace adj v (u :: neighbours v))
    pair;
  if Hashtbl.length adj > max_vars * 8 then []
  else begin
    let covered = Hashtbl.create 64 and out = ref [] in
    List.iter
      (fun (u, v) ->
        if not (Hashtbl.mem covered (u, v)) then begin
          let q = ref [ v; u ] in
          let cand = ref (List.filter (fun z -> List.mem z (neighbours v)) (neighbours u)) in
          while !cand <> [] do
            let score z = (-List.length (List.filter (fun y -> List.mem y !cand) (neighbours z)), z) in
            let w = List.fold_left (fun b z -> if score z < score b then z else b) (List.hd !cand) !cand in
            q := w :: !q;
            cand := List.filter (fun z -> z <> w && List.mem z (neighbours w)) !cand
          done;
          let q = List.rev !q in
          List.iter (fun a -> List.iter (fun b -> if a < b then Hashtbl.replace covered (a, b) ()) q) q;
          if List.length q >= 3 then out := q :: !out
        end)
      (List.sort compare (Hashtbl.fold (fun k _ acc -> k :: acc) pair []));
    List.map (fun q -> (q, pair)) (List.rev !out)
  end

(* −Σ_{q∈Q} x_q ≥ −1 from the pairwise exclusions, one variable at a time *)
let clique_cut bd q pair =
  let p a b = Hashtbl.find pair (min a b, max a b) in
  let q = Array.of_list q in
  let cur = ref (p q.(0) q.(1)) in
  for t = 2 to Array.length q - 1 do
    let s = add bd ((!cur, Z.of_int (t - 1)) :: List.init t (fun i -> (p q.(i) q.(t), Z.one))) in
    cur := div bd s (Z.of_int t)
  done;
  !cur

let result_of bd root strategy =
  if not (contradiction (Vec.get bd.vals root)) then failwith "internal: final line is not a contradiction";
  refutation ~measures:Measures.(empty |> text "strategy" strategy) (finish bd root)

(* each resolution step x∨C, ¬x∨D ⊢ C∨D becomes an addition, plus (when C
   and D share literals) the bounds of the other literals and a division by 2 *)
let simulate bd (clauses : Clause.t array) (lim : Limits.t) =
  let cnf = Cnf.make ~num_vars:bd.sys.num_vars (Array.to_list clauses) in
  match Resolution.dag ~lim cnf with
  | Refutation r ->
      let ax_of = Clause.Tbl.create 64 in
      Array.iteri (fun i c -> if not (Clause.Tbl.mem ax_of c) then Clause.Tbl.replace ax_of c i) clauses;
      let rl = r.proof.Resolution.lines in
      let at = Array.make (Array.length rl) 0 and root = ref 0 in
      Array.iteri
        (fun k (ln : Resolution.line) ->
          match ln.rule with
          | Resolution.Axiom -> at.(k) <- axiom bd (Clause.Tbl.find ax_of ln.clause)
          | Resolution.Res { pos = i; neg = j; pivot = x } ->
              let a = List.filter (( <> ) x) (Clause.lits rl.(i).clause) and b = List.filter (( <> ) (-x)) (Clause.lits rl.(j).clause) in
              let shared = List.filter (fun l -> List.mem l b) a in
              let kk =
                if shared = [] then add bd [ (at.(i), Z.one); (at.(j), Z.one) ]
                else begin
                  let singles = List.sort compare (List.filter (fun l -> not (List.mem l shared)) (a @ b)) in
                  div bd
                    (add bd ([ (at.(i), Z.one); (at.(j), Z.one) ] @ List.map (fun l -> (bound bd (abs l) (if l > 0 then Lo else Hi), Z.one)) singles))
                    (Z.of_int 2)
                end
              in
              at.(k) <- kk;
              root := kk)
        rl;
      result_of bd !root "resolution simulation"
  | Unknown u -> unknown ("resolution simulation: " ^ u.message)
  | Model m -> Model { m with message = "resolution simulation: " ^ m.message }

let search (lim : Limits.t) (sys : Ineq.t) =
  let deadline = Limits.deadline lim in
  let bd = { sys; lines = Vec.create (Axiom 0); vals = Vec.create { a = IM.empty; b = Z.zero }; bounds = Hashtbl.create 64; axioms = Hashtbl.create 64 } in
  let m = Array.length sys.ineqs in
  let rows = ref (List.init m (axiom bd)) in
  for v = 1 to sys.num_vars do
    rows := !rows @ [ bound bd v Lo; bound bd v Hi ]
  done;
  Array.iteri
    (fun i (q : Ineq.ineq) ->
      let g = List.fold_left (fun g (_, c) -> Z.gcd g (Z.of_int c)) Z.zero q.terms in
      if Z.gt g Z.one then rows := !rows @ [ div bd (axiom bd i) g ])
    sys.ineqs;
  let lp_result =
    try
      match lp bd !rows deadline with
      | Some l -> `Done (result_of bd l "gcd rounding + LP")
      | None -> (
          match cliques bd !rows (Option.value lim.max_vars ~default:64) with
          | [] -> `Next
          | qs -> (
              rows := !rows @ List.map (fun (q, pair) -> clique_cut bd q pair) qs;
              match lp bd !rows deadline with Some l -> `Done (result_of bd l "clique cuts + LP") | None -> `Next))
    with Clock.Timeout -> `Done (unknown budget_message)
  in
  match lp_result with
  | `Done r -> r
  | `Next -> (
      let cls = Array.map Encodings.ineq_as_clause sys.ineqs in
      if Array.exists Option.is_none cls then unknown "LP strategies failed; input is not clausal, so resolution simulation does not apply"
      else
        let left = Option.map (fun r -> Float.max 0.5 r) (Clock.remaining deadline) in
        try simulate bd (Array.map Option.get cls) (Limits.with_time left Limits.none) with Clock.Timeout -> unknown budget_message)

(* ------------------------------------------------------------ system *)
type config = unit
type input = Ineq.t
type lower_bound = Nothing.t

let name = "cutting-planes"
let version = "0.3"

let info =
  {
    group = "geometric";
    order = 100;
    line_type = "linear inequality";
    primary_metric = "size";
    book = "6.3";
    simulates = [ "resolution" ];
    description = "Cutting Planes; gcd rounding + clique cuts + exact LP, resolution simulation fallback";
  }

let language = Lang.Ineq
let encoding = Some "cnf-ineq"
let params = []
let variants = [ [] ]
let label _ = "CP"
let configure _ = Ok ()
let searches () = true
let search () lim sys = search lim sys
let proof = codec
let lower_bound = Nothing.codec
let verify () sys p = check sys p
let check_lower_bound = Nothing.check
let parse_text = None
