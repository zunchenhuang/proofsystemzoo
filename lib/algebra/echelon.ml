(* An incremental echelon basis with reduction traces.

   Vectors are inserted one at a time and top-reduced against the basis
   (their leading monomial is cancelled while it is the leading monomial of
   a basis vector). A vector that survives becomes a basis entry, normalised
   to leading coefficient 1, and remembers its reduction: the generator it
   came from, the scale it was divided by, and the (pivot, coefficient)
   pairs subtracted on the way. That trace is all that is needed to

   - [express] a target in the span as a combination of the inserted
     generators, by one back-substitution over the entries (instead of
     carrying a dense combination along with every basis vector), and
   - read each basis vector off as one linear step over earlier lines,
     which is how Polynomial Calculus derivations are extracted.

   [design] computes the dual object: a linear functional L with L(1) = 1
   that vanishes on the span, the lower-bound certificate of
   Nullstellensatz. *)

module Make (R : Ring.S) = struct
  module K = R.K
  module M = R.M

  module H = Hashtbl.Make (struct
    type t = M.t

    let equal = M.equal
    let hash = M.hash
  end)

  type entry = { vec : R.t; gen : int; scale : K.t; tj : int array; tc : K.t array }
  (* vec = (generator gen − Σₖ tc.(k)·vec(tj.(k))) / scale *)

  type t = { entries : entry Vec.t; pivots : int H.t; bj : int Vec.t; bc : K.t Vec.t }

  let dummy = { vec = R.zero; gen = -1; scale = K.one; tj = [||]; tc = [||] }

  let create () =
    { entries = Vec.create ~capacity:1024 dummy; pivots = H.create 4096; bj = Vec.create 0; bc = Vec.create K.zero }

  let rank t = Vec.length t.entries
  let entry t k = Vec.get t.entries k
  let pivot t m = H.find_opt t.pivots m
  let spans_one t = H.mem t.pivots M.one

  (* the residual of top-reduction; the trace is left in bj / bc *)
  let reduce t v =
    Vec.truncate t.bj 0;
    Vec.truncate t.bc 0;
    let rec go v =
      if R.is_zero v then v
      else
        match H.find_opt t.pivots (R.lead_mono v) with
        | None -> v
        | Some j ->
            let c = R.lead_coef v in
            ignore (Vec.push t.bj j);
            ignore (Vec.push t.bc c);
            go (R.axpy (K.neg c) (Vec.get t.entries j).vec v)
    in
    go v

  (* Some (entry index, leading monomial) if [v] is independent of the basis *)
  let add t v ~gen =
    let r = reduce t v in
    if R.is_zero r then None
    else begin
      let s = R.lead_coef r in
      let vec = R.scale (K.inv s) r in
      let lm = R.lead_mono vec in
      let k = Vec.push t.entries { vec; gen; scale = s; tj = Vec.to_array t.bj; tc = Vec.to_array t.bc } in
      H.replace t.pivots lm k;
      Some (k, lm)
    end

  let mem t v = R.is_zero (reduce t v)

  (* the coefficients c_g, sorted by generator, with target = Σ c_g·generator_g *)
  let express t target =
    let r = reduce t target in
    if not (R.is_zero r) then None
    else begin
      let n = rank t in
      let beta = Array.make n K.zero in
      for k = 0 to Vec.length t.bj - 1 do
        let j = Vec.get t.bj k in
        beta.(j) <- K.add beta.(j) (Vec.get t.bc k)
      done;
      let acc = Hashtbl.create 64 in
      for i = n - 1 downto 0 do
        if not (K.is_zero beta.(i)) then begin
          let e = Vec.get t.entries i in
          let b = K.div beta.(i) e.scale in
          Hashtbl.replace acc e.gen (K.add b (Option.value (Hashtbl.find_opt acc e.gen) ~default:K.zero));
          Array.iteri (fun k j -> beta.(j) <- K.sub beta.(j) (K.mul b e.tc.(k))) e.tj
        end
      done;
      Some
        (Hashtbl.fold (fun g c l -> if K.is_zero c then l else (g, c) :: l) acc []
        |> List.sort (fun (a, _) (b, _) -> Int.compare a b))
    end

  (* L with L(1) = 1 and L(b) = 0 for every basis vector b; None if 1 is in
     the span. Entries are processed by increasing leading monomial, so every
     other monomial of an entry already has its final value. *)
  let design t =
    if spans_one t then None
    else begin
      let n = rank t in
      let lead i = R.lead_mono (entry t i).vec in
      let order = Array.init n Fun.id in
      Array.sort (fun a b -> M.compare (lead a) (lead b)) order;
      let l = H.create ((2 * n) + 1) in
      H.replace l M.one K.one;
      Array.iter
        (fun i ->
          let v = (entry t i).vec in
          let s = ref K.zero in
          for k = 1 to R.size v - 1 do
            match H.find_opt l v.R.ms.(k) with Some x -> s := K.add !s (K.mul v.R.cs.(k) x) | None -> ()
          done;
          if not (K.is_zero !s) then H.replace l v.R.ms.(0) (K.neg !s))
        order;
      Some (H.fold (fun m c acc -> (m, c) :: acc) l [] |> List.sort (fun (a, _) (b, _) -> M.compare a b))
    end
end
