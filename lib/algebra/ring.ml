(* Multilinear polynomials K[x₁..xₙ]/(xᵢ² − xᵢ), as sorted parallel arrays.

   A polynomial is two arrays, monomials in strictly decreasing graded order
   (the leading term first) and their non-zero coefficients. The private type
   makes that invariant global: every value of type [t] was produced by this
   module. Addition and [axpy] are linear merges, multiplication by a
   variable is a merge of two order-preserving subsequences, and with [Word]
   monomials and GF(p) coefficients both arrays are unboxed integers. *)

module type S = sig
  module K : Field.S
  module M : Mono.S

  type t = private { ms : M.t array; cs : K.t array }

  val zero : t
  val one : t
  val is_zero : t -> bool
  val const : K.t -> t
  val monomial : M.t -> K.t -> t
  val of_terms : (M.t * K.t) list -> t
  val of_ints : (int list * int) list -> t
  val terms : t -> (M.t * K.t) list
  val size : t -> int
  val lead_mono : t -> M.t
  val lead_coef : t -> K.t
  val degree : t -> int
  val coef : t -> M.t -> K.t
  val add : t -> t -> t
  val sub : t -> t -> t
  val axpy : K.t -> t -> t -> t (* axpy a x y = a·x + y *)
  val scale : K.t -> t -> t
  val neg : t -> t
  val mul_var : int -> t -> t
  val mul_mono : M.t -> t -> t
  val mul : t -> t -> t
  val equal : t -> t -> bool
  val is_constant : t -> bool (* a non-zero constant *)
  val apply : (M.t -> K.t) -> t -> K.t (* Σ c·L(m) *)
  val support_vars : t -> int list
  val absorbing : t -> int list (* variables x with x·f ∈ {0, f} *)
  val to_string : t -> string
end

module Make (K : Field.S) (M : Mono.S) : S with module K = K and module M = M = struct
  module K = K
  module M = M

  type t = { ms : M.t array; cs : K.t array }

  let zero = { ms = [||]; cs = [||] }
  let is_zero f = Array.length f.ms = 0
  let const c = if K.is_zero c then zero else { ms = [| M.one |]; cs = [| c |] }
  let one = const K.one
  let monomial m c = if K.is_zero c then zero else { ms = [| m |]; cs = [| c |] }
  let size f = Array.length f.ms
  let terms f = List.init (size f) (fun i -> (f.ms.(i), f.cs.(i)))
  let lead_mono f = if is_zero f then invalid_arg "Ring.lead_mono: zero polynomial" else f.ms.(0)
  let lead_coef f = if is_zero f then invalid_arg "Ring.lead_coef: zero polynomial" else f.cs.(0)
  let degree f = if is_zero f then 0 else M.degree f.ms.(0)
  let shrink ms cs k = if k = Array.length ms then { ms; cs } else { ms = Array.sub ms 0 k; cs = Array.sub cs 0 k }

  (* sort decreasing, merge equal monomials, drop zero coefficients *)
  let normalize (a : (M.t * K.t) array) =
    Array.stable_sort (fun (x, _) (y, _) -> M.compare y x) a;
    let n = Array.length a in
    let ms = Array.make n M.one and cs = Array.make n K.zero in
    let k = ref 0 and i = ref 0 in
    while !i < n do
      let m = fst a.(!i) in
      let c = ref K.zero in
      while !i < n && M.equal (fst a.(!i)) m do
        c := K.add !c (snd a.(!i));
        incr i
      done;
      if not (K.is_zero !c) then begin
        ms.(!k) <- m;
        cs.(!k) <- !c;
        incr k
      end
    done;
    shrink ms cs !k

  let of_terms l = normalize (Array.of_list l)
  let of_ints l = of_terms (List.map (fun (vs, c) -> (M.of_list vs, K.of_int c)) l)

  let coef f m =
    let rec go lo hi =
      if lo >= hi then K.zero
      else
        let mid = (lo + hi) / 2 in
        let c = M.compare f.ms.(mid) m in
        if c = 0 then f.cs.(mid) else if c > 0 then go (mid + 1) hi else go lo mid
    in
    go 0 (size f)

  let scale a f = if K.is_zero a then zero else if K.is_one a then f else { ms = f.ms; cs = Array.map (K.mul a) f.cs }
  let neg f = { ms = f.ms; cs = Array.map K.neg f.cs }

  let axpy a x y =
    if K.is_zero a || is_zero x then y
    else if is_zero y then scale a x
    else begin
      let nx = size x and ny = size y in
      let ms = Array.make (nx + ny) M.one and cs = Array.make (nx + ny) K.zero in
      let i = ref 0 and j = ref 0 and k = ref 0 in
      let unit = K.is_one a in
      while !i < nx && !j < ny do
        let mx = Array.unsafe_get x.ms !i and my = Array.unsafe_get y.ms !j in
        let c = M.compare mx my in
        if c > 0 then begin
          ms.(!k) <- mx;
          cs.(!k) <- (if unit then x.cs.(!i) else K.mul a x.cs.(!i));
          incr k;
          incr i
        end
        else if c < 0 then begin
          ms.(!k) <- my;
          cs.(!k) <- y.cs.(!j);
          incr k;
          incr j
        end
        else begin
          let v = K.add (if unit then x.cs.(!i) else K.mul a x.cs.(!i)) y.cs.(!j) in
          if not (K.is_zero v) then begin
            ms.(!k) <- mx;
            cs.(!k) <- v;
            incr k
          end;
          incr i;
          incr j
        end
      done;
      while !i < nx do
        ms.(!k) <- x.ms.(!i);
        cs.(!k) <- (if unit then x.cs.(!i) else K.mul a x.cs.(!i));
        incr k;
        incr i
      done;
      while !j < ny do
        ms.(!k) <- y.ms.(!j);
        cs.(!k) <- y.cs.(!j);
        incr k;
        incr j
      done;
      shrink ms cs !k
    end

  let add x y = axpy K.one x y
  let sub x y = axpy (K.neg K.one) y x

  (* x·f: the terms that contain x stay, the others gain x; each of the two
     subsequences stays sorted (adding the same new variable preserves the
     graded order), so the product is one merge *)
  let mul_var v f =
    let n = size f in
    let ms = Array.make n M.one and cs = Array.make n K.zero in
    let xv = M.var v in
    let next_with i =
      let i = ref i in
      while !i < n && not (M.mem v f.ms.(!i)) do incr i done;
      !i
    and next_without i =
      let i = ref i in
      while !i < n && M.mem v f.ms.(!i) do incr i done;
      !i
    in
    let ia = ref (next_with 0) and ib = ref (next_without 0) and k = ref 0 in
    while !ia < n || !ib < n do
      if !ib >= n then begin
        ms.(!k) <- f.ms.(!ia);
        cs.(!k) <- f.cs.(!ia);
        incr k;
        ia := next_with (!ia + 1)
      end
      else begin
        let mb = M.mul f.ms.(!ib) xv in
        let c = if !ia >= n then -1 else M.compare f.ms.(!ia) mb in
        if c > 0 then begin
          ms.(!k) <- f.ms.(!ia);
          cs.(!k) <- f.cs.(!ia);
          incr k;
          ia := next_with (!ia + 1)
        end
        else if c < 0 then begin
          ms.(!k) <- mb;
          cs.(!k) <- f.cs.(!ib);
          incr k;
          ib := next_without (!ib + 1)
        end
        else begin
          let s = K.add f.cs.(!ia) f.cs.(!ib) in
          if not (K.is_zero s) then begin
            ms.(!k) <- mb;
            cs.(!k) <- s;
            incr k
          end;
          ia := next_with (!ia + 1);
          ib := next_without (!ib + 1)
        end
      end
    done;
    shrink ms cs !k

  let mul_mono m f =
    match M.degree m with
    | 0 -> f
    | 1 -> mul_var (List.hd (M.to_list m)) f
    | _ -> normalize (Array.init (size f) (fun i -> (M.mul m f.ms.(i), f.cs.(i))))

  let mul f g =
    if is_zero f || is_zero g then zero
    else begin
      let acc = Array.make (size f * size g) (M.one, K.zero) in
      for i = 0 to size f - 1 do
        for j = 0 to size g - 1 do
          acc.((i * size g) + j) <- (M.mul f.ms.(i) g.ms.(j), K.mul f.cs.(i) g.cs.(j))
        done
      done;
      normalize acc
    end

  let equal f g =
    size f = size g
    &&
    let ok = ref true in
    for i = 0 to size f - 1 do
      if not (M.equal f.ms.(i) g.ms.(i) && K.equal f.cs.(i) g.cs.(i)) then ok := false
    done;
    !ok

  let is_constant f = size f = 1 && M.equal f.ms.(0) M.one

  let apply l f =
    let s = ref K.zero in
    for i = 0 to size f - 1 do
      s := K.add !s (K.mul f.cs.(i) (l f.ms.(i)))
    done;
    !s

  let support_vars f = M.to_list (Array.fold_left M.mul M.one f.ms)

  let absorbing f =
    List.filter
      (fun x ->
        let xf = mul_var x f in
        is_zero xf || equal xf f)
      (support_vars f)

  let to_string f =
    if is_zero f then "0"
    else String.concat " + " (List.map (fun (m, c) -> K.to_string c ^ "·" ^ M.to_string m) (terms f))
end
