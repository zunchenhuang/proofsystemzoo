(* The Resolution family: one proof format and checker (resolution-dag/1)
   and three systems over it —

   - tree-resolution: DPLL decision-tree search with pruning;
   - ordered-resolution: Davis–Putnam variable elimination;
   - resolution (DAG): minimum-width saturation, then the other two, keeping
     the smallest proof.

   The checker enforces the extra structure of the restricted systems: no
   derived line used twice (tree-like), pivots along a declared variable
   order (ordered). *)
open System

let format = "resolution-dag/1"

type rule = Axiom | Res of { pos : int; neg : int; pivot : int }
type line = { clause : Clause.t; rule : rule }
type proof = { order : int list option; lines : line array }

(* ------------------------------------------------------------ codecs *)
let line_codec : line Json.codec =
  let open Json in
  let encode l =
    match l.rule with
    | Axiom -> E.obj [ ("c", E.ints (Clause.lits l.clause)); ("rule", `String "axiom") ]
    | Res r ->
        E.obj [ ("c", E.ints (Clause.lits l.clause)); ("rule", `String "res"); ("from", E.ints [ r.pos; r.neg ]); ("pivot", `Int r.pivot) ]
  in
  let decode j =
    let* lits = D.field "c" (D.list D.int) j in
    let* clause = in_context "c" (Clause.of_list_strict lits) in
    let* rule = rule_of j in
    match rule with
    | "axiom" -> Ok { clause; rule = Axiom }
    | "res" ->
        let* pos, neg = D.field "from" (D.pair D.int D.int) j in
        let+ pivot = D.field "pivot" D.int j in
        { clause; rule = Res { pos; neg; pivot } }
    | r -> error "unknown rule %S" r
  in
  codec encode decode

let codec : proof Json.codec =
  let open Json in
  let encode p =
    E.obj
      ([ ("format", `String format) ]
      @ (match p.order with Some o -> [ ("order", E.ints o) ] | None -> [])
      @ [ ("lines", E.array line_codec.encode p.lines) ])
  in
  let decode j =
    let* () = D.tag "format" format j in
    let* order = D.field_opt "order" (D.list D.int) j in
    let+ lines = D.field "lines" (D.array line_codec.decode) j in
    { order; lines }
  in
  codec encode decode

let measures (lines : line array) =
  let n = Array.length lines in
  let depth = Array.make n 0 in
  Array.iteri (fun k l -> match l.rule with Axiom -> () | Res r -> depth.(k) <- 1 + max depth.(r.pos) depth.(r.neg)) lines;
  let fold f = Array.fold_left f 0 lines in
  Measures.(
    empty
    |> int "size" n
    |> int "axioms_used" (fold (fun a l -> if l.rule = Axiom then a + 1 else a))
    |> int "width" (fold (fun a l -> max a (Clause.width l.clause)))
    |> int "derived_width" (fold (fun a l -> if l.rule = Axiom then a else max a (Clause.width l.clause)))
    |> int "depth" (if n = 0 then 0 else depth.(n - 1)))

(* ------------------------------------------------------------ checker *)
let check ?(tree_like = false) ?(ordered = false) (cnf : Cnf.t) (p : proof) : (Measures.t, string) result =
  let n = Array.length p.lines in
  let ( let* ) = Result.bind in
  let* () = System.check (n > 0) "no lines" in
  let* pos_in_order =
    if not ordered then Ok None
    else
      match p.order with
      | None -> Error "ordered resolution needs an \"order\""
      | Some o ->
          let h = Hashtbl.create 16 in
          List.iteri (fun k v -> Hashtbl.replace h v k) o;
          if Hashtbl.length h <> List.length o then Error "duplicate variable in order" else Ok (Some h)
  in
  let axioms = Cnf.clause_set cnf in
  let uses = Array.make n 0 in
  let line k =
    let l = p.lines.(k) in
    let* () = System.check (Clause.max_var l.clause <= cnf.num_vars) "line %d: unknown variable" k in
    match l.rule with
    | Axiom -> System.check (Clause.Tbl.mem axioms l.clause) "line %d: not an input clause" k
    | Res { pos = i; neg = j; pivot = v } ->
        let* () = System.check (0 <= i && i < k && 0 <= j && j < k && v > 0) "line %d: bad premise reference" k in
        let a = p.lines.(i).clause and b = p.lines.(j).clause in
        let* () = System.check (Clause.mem v a && Clause.mem (-v) b) "line %d: pivot x%d not complementary in premises" k v in
        let* () = System.check (Clause.equal l.clause (Clause.resolve a b v)) "line %d: clause is not the resolvent" k in
        let* () =
          match pos_in_order with
          | Some h when not (Hashtbl.mem h v) -> Error (Printf.sprintf "line %d: pivot x%d not in order" k v)
          | _ -> Ok ()
        in
        Seqx.iter_result
          (fun q ->
            match p.lines.(q).rule with
            | Axiom -> Ok ()
            | Res { pivot = pv; _ } ->
                uses.(q) <- uses.(q) + 1;
                let* () = System.check ((not tree_like) || uses.(q) <= 1) "line %d: derived line %d reused (not tree-like)" k q in
                let at x d = match pos_in_order with Some h -> Option.value (Hashtbl.find_opt h x) ~default:d | None -> 0 in
                System.check (pos_in_order = None || at pv max_int < at v (-1)) "line %d: pivot x%d out of order" k v)
          (List.to_seq [ i; j ])
  in
  let* () = Seqx.iter_result line (Seqx.range 0 n) in
  let* () = System.check (Clause.is_empty p.lines.(n - 1).clause) "last line is not the empty clause" in
  Ok (measures p.lines)

(* ancestors of [root], renumbered in their original order *)
let extract (get : int -> line) root : line array =
  let need = Hashtbl.create 64 in
  let stack = ref [ root ] in
  while !stack <> [] do
    let k = List.hd !stack in
    stack := List.tl !stack;
    if not (Hashtbl.mem need k) then begin
      Hashtbl.replace need k ();
      match (get k).rule with Res r -> stack := r.pos :: r.neg :: !stack | Axiom -> ()
    end
  done;
  let order = List.sort compare (Hashtbl.fold (fun k () acc -> k :: acc) need []) in
  let ren = Hashtbl.create 64 in
  List.iteri (fun i o -> Hashtbl.replace ren o i) order;
  Array.of_list
    (List.map
       (fun o ->
         let l = get o in
         match l.rule with
         | Axiom -> l
         | Res r -> { l with rule = Res { r with pos = Hashtbl.find ren r.pos; neg = Hashtbl.find ren r.neg } })
       order)

exception Stop of string
exception Sat of Assignment.t

(* ------------------------------------------------------ tree-like (DPLL) *)

(* Branch on the first free literal of the first clause with fewest free
   literals, the falsifying value first; a branch whose clause does not
   mention the branching literal is reused as it is (pruning). *)
let dpll ~deadline ~max_lines (cnf : Cnf.t) =
  let clauses = Array.map (fun c -> (c : Clause.t :> int array)) cnf.clauses in
  let n = cnf.num_vars in
  let rho = Array.make (n + 1) 0 in
  let value l = if l > 0 then rho.(l) else -rho.(-l) in
  let lines = Vec.create { clause = Clause.empty; rule = Axiom } in
  let emit l =
    let k = Vec.push lines l in
    if k >= max_lines then raise (Stop (Printf.sprintf "more than %d lines" max_lines));
    if k land 1023 = 0 then Clock.check deadline;
    k
  in
  let rec node () =
    let falsified = ref (-1) and best_free = ref max_int and best_lit = ref 0 in
    let nc = Array.length clauses and i = ref 0 in
    while !falsified < 0 && !i < nc do
      let c = clauses.(!i) in
      let sat = ref false and free = ref 0 and first = ref 0 and j = ref 0 in
      while (not !sat) && !j < Array.length c do
        let v = value c.(!j) in
        if v = 1 then sat := true
        else if v = 0 then begin
          if !free = 0 then first := c.(!j);
          incr free
        end;
        incr j
      done;
      if not !sat then
        if !free = 0 then falsified := !i
        else if !free < !best_free then begin
          best_free := !free;
          best_lit := !first
        end;
      incr i
    done;
    if !falsified >= 0 then
      let c = cnf.clauses.(!falsified) in
      (emit { clause = c; rule = Axiom }, c)
    else if !best_lit = 0 then raise (Sat (Assignment.make n (fun v -> rho.(v) = 1)))
    else begin
      let x = abs !best_lit in
      let first = !best_lit < 0 in
      let branch b =
        rho.(x) <- (if b then 1 else -1);
        let r = node () in
        rho.(x) <- 0;
        r
      in
      let ia, ca = branch first in
      let fa = if first then -x else x in
      if not (Clause.mem fa ca) then (ia, ca)
      else begin
        let ib, cb = branch (not first) in
        if not (Clause.mem (-fa) cb) then (ib, cb)
        else begin
          let pos, neg, pc, nc = if fa = x then (ia, ib, ca, cb) else (ib, ia, cb, ca) in
          let r = Clause.resolve pc nc x in
          (emit { clause = r; rule = Res { pos; neg; pivot = x } }, r)
        end
      end
    end
  in
  match node () with
  | root, _ ->
      let lines = extract (Vec.get lines) root in
      refutation ~measures:(measures lines) { order = None; lines }
  | exception Sat a -> model ~witness:a "DPLL found a satisfying assignment"
  | exception Stop s -> unknown ~measures:Measures.(empty |> int "lines_explored" (Vec.length lines)) s

(* ------------------------------------------- ordered (Davis–Putnam) *)

(* Eliminate the variable minimising |pos|·|neg| − |pos| − |neg|; resolvents
   that are tautologies or subsumed by an active clause are dropped. *)
let davis_putnam ~deadline ~max_clauses (cnf : Cnf.t) =
  let clauses = Vec.create Clause.empty and rules = Vec.create Axiom in
  let active = Hashtbl.create 256 and index = Clause.Tbl.create 256 in
  let heads : (int, int list) Hashtbl.t = Hashtbl.create 256 in
  let subsumed r =
    List.exists
      (fun l ->
        List.exists
          (fun k -> Hashtbl.mem active k && Clause.subset (Vec.get clauses k) r)
          (Option.value (Hashtbl.find_opt heads l) ~default:[]))
      (Clause.lits r)
  in
  let add c rule =
    match Clause.Tbl.find_opt index c with
    | Some k when Hashtbl.mem active k -> Some k
    | _ ->
        if rule <> Axiom && subsumed c then None
        else begin
          let k = Vec.push clauses c in
          ignore (Vec.push rules rule);
          Clause.Tbl.replace index c k;
          Hashtbl.replace active k ();
          (match Clause.lits c with h :: _ -> Hashtbl.replace heads h (k :: Option.value (Hashtbl.find_opt heads h) ~default:[]) | [] -> ());
          if Vec.length clauses > max_clauses then raise (Stop (Printf.sprintf "more than %d clauses" max_clauses));
          Some k
        end
  in
  let removed = Hashtbl.create 32 and order = ref [] in
  let get k = { clause = Vec.get clauses k; rule = Vec.get rules k } in
  let finish root =
    let lines = extract get root in
    let used = Array.fold_left (fun acc l -> match l.rule with Res r -> r.pivot :: acc | Axiom -> acc) [] lines in
    let o = List.filter (fun v -> List.mem v used) (List.rev !order) in
    refutation ~measures:Measures.(empty |> int "clauses_generated" (Vec.length clauses)) { order = Some o; lines }
  in
  let assignment () =
    let value = Array.make (cnf.num_vars + 1) 0 in
    let sat c = List.exists (fun l -> value.(abs l) = if l > 0 then 1 else -1) (Clause.lits c) in
    List.iter
      (fun x ->
        value.(x) <- -1;
        if not (List.for_all sat (Hashtbl.find removed x)) then value.(x) <- 1)
      !order;
    Assignment.make cnf.num_vars (fun v -> value.(v) = 1)
  in
  let eliminated () = Measures.(empty |> int "eliminated" (List.length !order)) in
  try
    let early = ref None in
    Array.iter
      (fun c ->
        if !early = None && not (Clause.is_tautology c) then
          match add c Axiom with Some k when Clause.is_empty c -> early := Some k | _ -> ())
      cnf.clauses;
    match !early with
    | Some k -> finish k
    | None ->
        let rec loop () =
          let occ = Hashtbl.create 64 in
          let ids = List.sort compare (Hashtbl.fold (fun k () acc -> k :: acc) active []) in
          List.iter
            (fun k -> List.iter (fun l -> Hashtbl.replace occ l (k :: Option.value (Hashtbl.find_opt occ l) ~default:[])) (Clause.lits (Vec.get clauses k)))
            ids;
          let vars = List.sort_uniq compare (Hashtbl.fold (fun l _ acc -> abs l :: acc) occ []) in
          match vars with
          | [] -> model ~witness:(assignment ()) ~measures:(eliminated ()) "all variables eliminated without the empty clause"
          | v0 :: _ -> (
              let cnt l = List.length (Option.value (Hashtbl.find_opt occ l) ~default:[]) in
              let score v = ((cnt v * cnt (-v)) - cnt v - cnt (-v), v) in
              let x = List.fold_left (fun b v -> if score v < score b then v else b) v0 vars in
              let p = List.sort compare (Option.value (Hashtbl.find_opt occ x) ~default:[])
              and nn = List.sort compare (Option.value (Hashtbl.find_opt occ (-x)) ~default:[]) in
              order := x :: !order;
              Hashtbl.replace removed x (List.map (Vec.get clauses) (p @ nn));
              List.iter (Hashtbl.remove active) (p @ nn);
              let found = ref None in
              List.iter
                (fun i ->
                  if !found = None then begin
                    List.iter
                      (fun j ->
                        if !found = None then begin
                          let r = Clause.resolve (Vec.get clauses i) (Vec.get clauses j) x in
                          if not (Clause.is_tautology r) then
                            match add r (Res { pos = i; neg = j; pivot = x }) with
                            | Some k when Clause.is_empty r -> found := Some k
                            | _ -> ()
                        end)
                      nn;
                    Clock.check deadline
                  end)
                p;
              match !found with Some k -> finish k | None -> loop ())
        in
        loop ()
  with
  | Stop s -> unknown ~measures:(eliminated ()) s
  | Clock.Timeout -> unknown ~measures:(eliminated ()) budget_message

(* ------------------------------------- DAG: width-bounded saturation *)

module Heap = Set.Make (struct
  type t = int * int

  let compare (a, b) (c, d) =
    let x = Int.compare a c in
    if x <> 0 then x else Int.compare b d
end)

type saturation = { root : int option; bound_hit : bool; generated : int; get : int -> line }

(* All resolvents of width ≤ w, narrowest clause first, forward-subsumed
   ones dropped (a clause subsumed by a stored one is never stored). *)
let saturate ~deadline ~max_clauses (axioms : Clause.t list) w : saturation =
  let cls = Vec.create Clause.empty and rules = Vec.create Axiom in
  let seen = Clause.Tbl.create 1024 in
  let by_head : (int, Clause.t list) Hashtbl.t = Hashtbl.create 256 in
  let occurs : (int, int list) Hashtbl.t = Hashtbl.create 256 in
  let heap = ref Heap.empty and bound_hit = ref false in
  let subsumed c =
    List.exists (fun l -> List.exists (fun d -> Clause.subset d c) (Option.value (Hashtbl.find_opt by_head l) ~default:[])) (Clause.lits c)
  in
  let add c rule =
    if Clause.Tbl.mem seen c || (rule <> Axiom && subsumed c) then None
    else begin
      let k = Vec.push cls c in
      ignore (Vec.push rules rule);
      Clause.Tbl.replace seen c k;
      (match Clause.lits c with h :: _ -> Hashtbl.replace by_head h (c :: Option.value (Hashtbl.find_opt by_head h) ~default:[]) | [] -> ());
      heap := Heap.add (Clause.width c, k) !heap;
      if Vec.length cls > max_clauses then raise (Stop (Printf.sprintf "more than %d clauses at width bound %d" max_clauses w));
      Some k
    end
  in
  let result root = { root; bound_hit = !bound_hit; generated = Vec.length cls; get = (fun k -> { clause = Vec.get cls k; rule = Vec.get rules k }) } in
  let early = ref None in
  List.iter (fun a -> if !early = None then match add a Axiom with Some k when Clause.is_empty a -> early := Some k | _ -> ()) axioms;
  match !early with
  | Some k -> result (Some k)
  | None ->
      let steps = ref 0 in
      let rec loop () =
        if Heap.is_empty !heap then result None
        else begin
          let ((_, k) as e) = Heap.min_elt !heap in
          heap := Heap.remove e !heap;
          let c = Vec.get cls k in
          let found = ref None in
          List.iter
            (fun lit ->
              if !found = None then
                List.iter
                  (fun j ->
                    if !found = None then begin
                      let r = Clause.resolve c (Vec.get cls j) lit in
                      if not (Clause.is_tautology r) then
                        if Clause.width r > w then bound_hit := true
                        else
                          let pos, neg = if lit > 0 then (k, j) else (j, k) in
                          match add r (Res { pos; neg; pivot = abs lit }) with
                          | Some idx when Clause.is_empty r -> found := Some idx
                          | _ -> ()
                    end)
                  (List.rev (Option.value (Hashtbl.find_opt occurs (-lit)) ~default:[])))
            (Clause.lits c);
          match !found with
          | Some idx -> result (Some idx)
          | None ->
              List.iter (fun lit -> Hashtbl.replace occurs lit (k :: Option.value (Hashtbl.find_opt occurs lit) ~default:[])) (Clause.lits c);
              incr steps;
              if !steps land 255 = 0 then Clock.check deadline;
              loop ()
        end
      in
      loop ()

(* the least w for which width-w saturation derives the empty clause *)
let min_width ~deadline ~max_clauses ~max_width (cnf : Cnf.t) =
  let axioms = List.filter (fun c -> not (Clause.is_tautology c)) (Array.to_list cnf.clauses) in
  let top = match max_width with None -> cnf.num_vars | Some w -> min w cnf.num_vars in
  let lb w = Measures.(empty |> int "derived_width_lb" w) in
  let rec go w =
    if w > top then unknown ~measures:(lb (top + 1)) (Printf.sprintf "no refutation with derived width <= %d" top)
    else
      match saturate ~deadline ~max_clauses axioms w with
      | exception Stop s -> unknown ~measures:(lb w) s
      | exception Clock.Timeout -> unknown ~measures:(lb w) budget_message
      | { root = Some r; get; generated; _ } ->
          let lines = extract get r in
          refutation ~measures:Measures.(empty |> int "width_bound" w |> int "clauses_generated" generated) { order = None; lines }
      | { bound_hit = false; generated; _ } ->
          model ~measures:Measures.(empty |> int "clauses_generated" generated) (Printf.sprintf "saturation closed at width %d without the empty clause" w)
      | _ -> go (w + 1)
  in
  go 0

let size_of = function Refutation r -> Array.length r.proof.lines | _ -> max_int

(* minimum-width saturation with 60% of the budget, then Davis–Putnam and
   DPLL with half of what is left each; the smallest proof wins *)
let dag ~(lim : Limits.t) (cnf : Cnf.t) =
  let budget = lim.time and t0 = Clock.now () in
  let left fraction = Option.map (fun b -> Clock.now () +. (fraction *. Float.max 1.0 (b -. (Clock.now () -. t0)))) budget in
  let deadline = Option.map (fun b -> t0 +. (0.6 *. b)) budget in
  let first = min_width ~deadline ~max_clauses:(Limits.size lim 200_000) ~max_width:lim.max_width cnf in
  match first with
  | Model m -> (
      match dpll ~deadline:(left 1.0) ~max_lines:300_000 cnf with
      | Model w -> Model { m with witness = w.witness }
      | _ | (exception Clock.Timeout) -> first)
  | _ ->
      let candidates =
        [
          ("ordered-resolution", fun () -> davis_putnam ~deadline:(left 0.5) ~max_clauses:300_000 cnf);
          ("tree-resolution", fun () -> try dpll ~deadline:(left 0.5) ~max_lines:300_000 cnf with Clock.Timeout -> unknown budget_message);
        ]
      in
      let best =
        List.fold_left
          (fun best (name, run) ->
            match run () with
            | Refutation r as o when size_of o < size_of best ->
                Refutation { r with proof = { r.proof with order = None }; measures = Measures.text "strategy" name r.measures }
            | _ -> best)
          first candidates
      in
      match (first, best) with
      | Refutation f, Refutation b ->
          let strategy = if Measures.mem "strategy" b.measures then b.measures else Measures.text "strategy" "min-width saturation" b.measures in
          let mw = match Measures.find_int "width" (measures f.proof.lines) with Some w -> Measures.int "min_width" w strategy | None -> strategy in
          Refutation { b with measures = mw }
      | Unknown u, Refutation b -> (
          match Measures.find_int "derived_width_lb" u.measures with
          | Some w -> Refutation { b with measures = Measures.int "derived_width_lb" w b.measures }
          | None -> best)
      | _ -> best

(* ------------------------------------------------------------ systems *)

module type FLAVOUR = sig
  val name : string
  val label : string
  val order : int
  val description : string
  val simulates : string list
  val tree_like : bool
  val ordered : bool
  val search : Limits.t -> Cnf.t -> (proof, Nothing.t) outcome
end

module Make (F : FLAVOUR) : S with type config = unit and type input = Cnf.t and type proof = proof and type lower_bound = Nothing.t = struct
  type config = unit
  type input = Cnf.t
  type nonrec proof = proof
  type lower_bound = Nothing.t

  let name = F.name
  let version = "0.3"

  let info =
    { group = "logical"; order = F.order; line_type = "clause"; primary_metric = "size"; book = "5"; simulates = F.simulates; description = F.description }

  let language = Lang.Cnf
  let encoding = None
  let params = []
  let variants = [ [] ]
  let label _ = F.label
  let configure _ = Ok ()
  let searches () = true
  let search () lim cnf = F.search lim cnf
  let proof = codec
  let lower_bound = Nothing.codec
  let verify () cnf p = check ~tree_like:F.tree_like ~ordered:F.ordered cnf p
  let check_lower_bound = Nothing.check
  let parse_text = None
end

module Tree = Make (struct
  let name = "tree-resolution"
  let label = "tree"
  let order = 1
  let description = "Tree-like Resolution; DPLL decision-tree search with pruning"
  let simulates = [ "truth-table" ]
  let tree_like = true
  let ordered = false

  let search (lim : Limits.t) cnf =
    try dpll ~deadline:(Limits.deadline lim) ~max_lines:(Limits.size lim 300_000) cnf with Clock.Timeout -> unknown budget_message
end)

module Ordered = Make (struct
  let name = "ordered-resolution"
  let label = "ord"
  let order = 2
  let description = "Ordered (Davis–Putnam) Resolution; variable-elimination search"
  let simulates = []
  let tree_like = false
  let ordered = true
  let search (lim : Limits.t) cnf = davis_putnam ~deadline:(Limits.deadline lim) ~max_clauses:(Limits.size lim 300_000) cnf
end)

module Dag = Make (struct
  let name = "resolution"
  let label = "res"
  let order = 3
  let description = "Resolution (DAG); min-width saturation + Davis–Putnam + DPLL portfolio, smallest proof kept"
  let simulates = [ "tree-resolution"; "ordered-resolution"; "truth-table" ]
  let tree_like = false
  let ordered = false
  let search lim cnf = dag ~lim cnf
end)
