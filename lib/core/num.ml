(* Small arithmetic helpers. *)

let is_prime p = p >= 2 && (let rec go k = k * k > p || (p mod k <> 0 && go (k + 1)) in go 2)

(* Best rational approximation of [x] with denominator at most [maxden]
   (by continued fractions). *)
let limit_denominator (x : Q.t) (maxden : Z.t) : Q.t =
  if Z.leq (Q.den x) maxden then x
  else begin
    let p0 = ref Z.zero and q0 = ref Z.one and p1 = ref Z.one and q1 = ref Z.zero in
    let n = ref (Q.num x) and d = ref (Q.den x) in
    (try
       while true do
         let a = Z.fdiv !n !d in
         let q2 = Z.add !q0 (Z.mul a !q1) in
         if Z.gt q2 maxden then raise Exit;
         let p2 = Z.add !p0 (Z.mul a !p1) in
         p0 := !p1;
         q0 := !q1;
         p1 := p2;
         q1 := q2;
         let r = Z.sub !n (Z.mul a !d) in
         n := !d;
         d := r;
         if Z.equal !d Z.zero then raise Exit
       done
     with Exit -> ());
    if Z.equal !q1 Z.zero then Q.of_bigint (Z.fdiv (Q.num x) (Q.den x))
    else begin
      let k = Z.fdiv (Z.sub maxden !q0) !q1 in
      let b1 = Q.make (Z.add !p0 (Z.mul k !p1)) (Z.add !q0 (Z.mul k !q1)) in
      let b2 = Q.make !p1 !q1 in
      if Q.leq (Q.abs (Q.sub b2 x)) (Q.abs (Q.sub b1 x)) then b2 else b1
    end
  end

let rationalize ?(maxden = Z.of_int 1_000_000) (f : float) : Q.t =
  if Float.is_integer f && Float.abs f < 4e18 then Q.of_int (int_of_float f)
  else limit_denominator (Q.of_float f) maxden

(* smallest positive integer vector proportional to a nonnegative rational vector *)
let integral (y : Q.t array) : Z.t array =
  let den = Array.fold_left (fun d v -> if Q.sign v = 0 then d else Z.lcm d (Q.den v)) Z.one y in
  let ints = Array.map (fun v -> Q.to_bigint (Q.mul v (Q.of_bigint den))) y in
  let g = Array.fold_left Z.gcd Z.zero ints in
  if Z.leq g Z.one then ints else Array.map (fun v -> Z.divexact v g) ints
