(* Polynomial Calculus and PCR over GF(p): exact minimum-degree search by
   incremental degree-d closure, with derivation extraction. Proof format
   pc/1:

     {"format": "pc/1", "p": p, "lines": [
        {"rule": "axiom", "ax": i}
      | {"rule": "mul", "var": x, "from": j}            x · line j
      | {"rule": "lin", "from": [[j, c], ...]}         Σ c · line j
     ]}

   ending in a non-zero constant. The degree of a proof is the largest
   degree of a line, a multiplication counting as the degree of its premise
   plus one. PCR is the same system over the cnf-poly-twin encoding (a twin
   variable x̄ = 1 − x for every x), where clauses become monomials.

   The search keeps one echelon basis across degrees: the degree-d closure
   contains the degree-(d−1) closure, so moving to degree d only adds the
   axioms of degree d and multiplies the basis vectors of degree d−1. Each
   basis vector is emitted as one "lin" line read off its reduction trace. *)
open System

let format = "pc/1"

type line = Axiom of int | Mul of { var : int; from : int } | Lin of (int * int) list
type proof = { p : int; lines : line array }

let line_codec : line Json.codec =
  let open Json in
  let encode = function
    | Axiom i -> E.obj [ ("rule", `String "axiom"); ("ax", `Int i) ]
    | Mul { var; from } -> E.obj [ ("rule", `String "mul"); ("var", `Int var); ("from", `Int from) ]
    | Lin from -> E.obj [ ("rule", `String "lin"); ("from", E.list (fun (j, c) -> E.ints [ j; c ]) from) ]
  in
  let decode j =
    let* rule = rule_of j in
    match rule with
    | "axiom" -> Result.map (fun i -> Axiom i) (D.field "ax" D.int j)
    | "mul" ->
        let* var = D.field "var" D.int j in
        let+ from = D.field "from" D.int j in
        Mul { var; from }
    | "lin" -> Result.map (fun l -> Lin l) (D.field "from" (D.list (D.pair D.int D.int)) j)
    | r -> error "unknown rule %S" r
  in
  codec encode decode

let codec : proof Json.codec =
  let open Json in
  codec
    (fun pr -> E.obj [ ("format", `String format); ("p", `Int pr.p); ("lines", E.array line_codec.encode pr.lines) ])
    (fun j ->
      let* () = D.tag "format" format j in
      let* p = D.field "p" D.int j in
      let+ lines = D.field "lines" (D.array line_codec.decode) j in
      { p; lines })

exception Stop of string

module Algo (K : Algebraic.GF) (M : Mono.S) = struct
  module R = Ring.Make (K) (M)
  module E = Echelon.Make (R)

  let p = K.characteristic
  let of_poly (f : Poly.poly) = R.of_ints (Poly.terms f)

  type gen = Gax of int | Gmul of int * int (* variable, basis entry *)

  (* the derivation of basis entry [final]: every entry it depends on,
     through traces and multiplications, in creation order *)
  let extract ech (gens : gen Vec.t) final : line array =
    let need = Hashtbl.create 64 in
    let stack = ref [ final ] in
    while !stack <> [] do
      let k = List.hd !stack in
      stack := List.tl !stack;
      if not (Hashtbl.mem need k) then begin
        Hashtbl.replace need k ();
        let e = E.entry ech k in
        stack := Array.to_list e.E.tj @ !stack;
        match Vec.get gens e.E.gen with Gmul (_, k') -> stack := k' :: !stack | Gax _ -> ()
      end
    done;
    let out = Vec.create (Axiom 0) and at = Hashtbl.create 64 in
    List.iter
      (fun k ->
        let e = E.entry ech k in
        let g =
          match Vec.get gens e.E.gen with
          | Gax i -> Vec.push out (Axiom i)
          | Gmul (x, k') -> Vec.push out (Mul { var = x; from = Hashtbl.find at k' })
        in
        if Array.length e.E.tj = 0 && K.is_one e.E.scale then Hashtbl.replace at k g
        else begin
          let inv = K.inv e.E.scale in
          let from = (g, K.to_int inv) :: Array.to_list (Array.mapi (fun q j -> (Hashtbl.find at j, K.to_int (K.neg (K.mul e.E.tc.(q) inv)))) e.E.tj) in
          Hashtbl.replace at k (Vec.push out (Lin from))
        end)
      (List.sort compare (Hashtbl.fold (fun k () acc -> k :: acc) need []));
    Vec.to_array out

  let search (lim : Limits.t) (ps : Poly.t) =
    let n = ps.num_vars in
    let top = match lim.max_degree with None -> n | Some d -> min d n in
    let max_lines = Limits.size lim 200_000 and deadline = Limits.deadline lim in
    let fs = Array.map of_poly ps.polys in
    let ech = E.create () and gens = Vec.create (Gax 0) and queue = Queue.create () in
    let d = ref 0 and final = ref (-1) in
    let insert vec g =
      let gid = Vec.push gens g in
      if gid >= max_lines then raise (Stop (Printf.sprintf "more than %d lines at degree %d" max_lines !d));
      match E.add ech vec ~gen:gid with
      | Some (k, lm) ->
          if M.degree lm <= !d - 1 then Queue.add k queue;
          if M.equal lm M.one then final := k
      | None -> ()
    in
    let rec stage dd =
      if dd > top then
        if top = n then model (Printf.sprintf "1 not derivable at degree n=%d" n)
        else unknown ~measures:Measures.(empty |> int "degree_lb" (top + 1)) (Printf.sprintf "no refutation of degree <= %d" top)
      else begin
        d := dd;
        for k = 0 to E.rank ech - 1 do
          if M.degree (R.lead_mono (E.entry ech k).E.vec) = dd - 1 then Queue.add k queue
        done;
        Array.iteri (fun i f -> if !final < 0 && (not (R.is_zero f)) && R.degree f = dd then insert f (Gax i)) fs;
        while !final < 0 && not (Queue.is_empty queue) do
          let k = Queue.pop queue in
          let b = (E.entry ech k).E.vec in
          let x = ref 1 in
          while !final < 0 && !x <= n do
            let prod = R.mul_var !x b in
            if (not (R.is_zero prod)) && not (R.equal prod b) then insert prod (Gmul (!x, k));
            incr x
          done;
          Clock.check deadline
        done;
        if !final >= 0 then
          refutation ~measures:Measures.(empty |> int "degree_bound" dd |> int "closure" (Vec.length gens)) { p; lines = extract ech gens !final }
        else stage (dd + 1)
      end
    in
    try stage 0 with
    | Stop s -> unknown ~measures:Measures.(empty |> int "degree_lb" !d) s
    | Clock.Timeout -> unknown ~measures:Measures.(empty |> int "degree_lb" !d) budget_message

  let verify (ps : Poly.t) (pr : proof) =
    if pr.p <> p then Error "proof is over another field"
    else if Array.length pr.lines = 0 then Error "no lines"
    else begin
      let n = Array.length pr.lines in
      let vals = Array.make n R.zero and deg = ref 0 in
      let line k =
        let ref_ok j = j >= 0 && j < k in
        let ( let* ) = Result.bind in
        let* v =
          match pr.lines.(k) with
          | Axiom i ->
              if i < 0 || i >= Array.length ps.polys then Error (Printf.sprintf "line %d: no input polynomial %d" k i) else Ok (of_poly ps.polys.(i))
          | Lin from ->
              if List.exists (fun (j, _) -> not (ref_ok j)) from then Error (Printf.sprintf "line %d: bad reference" k)
              else Ok (List.fold_left (fun acc (j, c) -> R.axpy (K.of_int c) vals.(j) acc) R.zero from)
          | Mul { var; from } ->
              if (not (ref_ok from)) || var < 1 || var > ps.num_vars then Error (Printf.sprintf "line %d: bad multiplication" k)
              else begin
                deg := max !deg (R.degree vals.(from) + 1);
                Ok (R.mul_var var vals.(from))
              end
        in
        vals.(k) <- v;
        deg := max !deg (R.degree v);
        Ok ()
      in
      match Seqx.iter_result line (Seqx.range 0 n) with
      | Error e -> Error e
      | Ok () ->
          if not (R.is_constant vals.(n - 1)) then Error "last line is not a non-zero constant"
          else Ok Measures.(empty |> int "degree" !deg |> int "size" n |> int "monomials" (Array.fold_left (fun s v -> s + R.size v) 0 vals))
    end
end

module type CORE = sig
  val search : Limits.t -> Poly.t -> (proof, Nothing.t) outcome
  val verify : Poly.t -> proof -> (Measures.t, string) result
end

module Core (K : Algebraic.GF) : CORE = struct
  let search lim (ps : Poly.t) =
    let (module M) = Mono.for_vars ps.num_vars in
    let module A = Algo (K) (M) in
    A.search lim ps

  let verify (ps : Poly.t) pr =
    let (module M) = Mono.for_vars ps.num_vars in
    let module A = Algo (K) (M) in
    A.verify ps pr
end

module type FLAVOUR = sig
  val name : string
  val abbrev : string
  val order : int
  val encoding : string
  val simulates : string list
  val description : string
end

module Make (F : FLAVOUR) : S with type config = (module CORE) and type input = Poly.t and type proof = proof and type lower_bound = Nothing.t = struct
  type config = (module CORE)
  type input = Poly.t
  type nonrec proof = proof
  type lower_bound = Nothing.t

  let name = F.name
  let version = "0.3"

  let info =
    { group = "algebraic"; order = F.order; line_type = "polynomial"; primary_metric = "degree"; book = "6.2"; simulates = F.simulates; description = F.description }

  let language = Lang.Poly
  let encoding = Some F.encoding
  let params = [ Algebraic.p_param ]
  let variants = [ [ ("p", "2") ]; [ ("p", "3") ] ]
  let label env = F.abbrev ^ Param.get env "p"

  let configure env =
    let (module K) = Algebraic.field_of_env env in
    Ok (module Core (K) : CORE)

  let searches _ = true
  let search ((module C) : config) lim ps = C.search lim ps
  let proof = codec
  let lower_bound = Nothing.codec
  let verify ((module C) : config) ps pr = C.verify ps pr
  let check_lower_bound _ = Nothing.check ()
  let parse_text = None
end

module Pc = Make (struct
  let name = "polynomial-calculus"
  let abbrev = "PC"
  let order = 1
  let encoding = "cnf-poly"
  let simulates = [ "nullstellensatz" ]
  let description = "Polynomial Calculus over GF(p); exact minimum-degree search"
end)

module Pcr = Make (struct
  let name = "pcr"
  let abbrev = "PCR"
  let order = 2
  let encoding = "cnf-poly-twin"
  let simulates = [ "polynomial-calculus"; "resolution" ]
  let description = "Polynomial Calculus with Resolution over GF(p) (twin variables); exact minimum-degree search"
end)
