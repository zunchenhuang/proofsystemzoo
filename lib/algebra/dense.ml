(* Dense floating-point linear algebra for the SDP: Cholesky factorisation
   and the symmetric eigenproblem (Householder tridiagonalisation followed
   by the implicit QL method). Matrices are arrays of unboxed float rows. *)

type mat = float array array

let make n m = Array.init n (fun _ -> Array.make m 0.0)
let copy (a : mat) = Array.map Array.copy a

(* lower-triangular L with a = L·Lᵀ (a symmetric positive definite);
   pivots below [floor] are raised to it *)
let cholesky ?(floor = 1e-12) (a : mat) : mat =
  let n = Array.length a in
  let l = make n n in
  for j = 0 to n - 1 do
    let s = ref a.(j).(j) in
    let lj = l.(j) in
    for k = 0 to j - 1 do
      s := !s -. (lj.(k) *. lj.(k))
    done;
    let d = sqrt (Float.max !s floor) in
    lj.(j) <- d;
    for i = j + 1 to n - 1 do
      let li = l.(i) in
      let s = ref a.(i).(j) in
      for k = 0 to j - 1 do
        s := !s -. (li.(k) *. lj.(k))
      done;
      li.(j) <- !s /. d
    done
  done;
  l

(* solve L·Lᵀ·x = b *)
let chol_solve (l : mat) (b : float array) =
  let n = Array.length l in
  let y = Array.copy b in
  for i = 0 to n - 1 do
    let li = l.(i) in
    let s = ref y.(i) in
    for k = 0 to i - 1 do
      s := !s -. (li.(k) *. y.(k))
    done;
    y.(i) <- !s /. li.(i)
  done;
  for i = n - 1 downto 0 do
    let s = ref y.(i) in
    for k = i + 1 to n - 1 do
      s := !s -. (l.(k).(i) *. y.(k))
    done;
    y.(i) <- !s /. l.(i).(i)
  done;
  y

(* Householder reduction of a symmetric matrix to tridiagonal form: a is
   overwritten by the orthogonal transformation, d gets the diagonal and e
   the subdiagonal (e.(0) = 0) *)
let tred2 (a : mat) (d : float array) (e : float array) =
  let n = Array.length a in
  for i = n - 1 downto 1 do
    let l = i - 1 in
    let h = ref 0.0 and scale = ref 0.0 in
    if l > 0 then begin
      for k = 0 to l do
        scale := !scale +. Float.abs a.(i).(k)
      done;
      if !scale = 0.0 then e.(i) <- a.(i).(l)
      else begin
        for k = 0 to l do
          a.(i).(k) <- a.(i).(k) /. !scale;
          h := !h +. (a.(i).(k) *. a.(i).(k))
        done;
        let f = a.(i).(l) in
        let g = if f >= 0.0 then -.sqrt !h else sqrt !h in
        e.(i) <- !scale *. g;
        h := !h -. (f *. g);
        a.(i).(l) <- f -. g;
        let f = ref 0.0 in
        for j = 0 to l do
          a.(j).(i) <- a.(i).(j) /. !h;
          let g = ref 0.0 in
          for k = 0 to j do
            g := !g +. (a.(j).(k) *. a.(i).(k))
          done;
          for k = j + 1 to l do
            g := !g +. (a.(k).(j) *. a.(i).(k))
          done;
          e.(j) <- !g /. !h;
          f := !f +. (e.(j) *. a.(i).(j))
        done;
        let hh = !f /. (!h +. !h) in
        for j = 0 to l do
          let f = a.(i).(j) in
          let g = e.(j) -. (hh *. f) in
          e.(j) <- g;
          for k = 0 to j do
            a.(j).(k) <- a.(j).(k) -. ((f *. e.(k)) +. (g *. a.(i).(k)))
          done
        done
      end
    end
    else e.(i) <- a.(i).(l);
    d.(i) <- !h
  done;
  d.(0) <- 0.0;
  e.(0) <- 0.0;
  for i = 0 to n - 1 do
    let l = i - 1 in
    if d.(i) <> 0.0 then
      for j = 0 to l do
        let g = ref 0.0 in
        for k = 0 to l do
          g := !g +. (a.(i).(k) *. a.(k).(j))
        done;
        for k = 0 to l do
          a.(k).(j) <- a.(k).(j) -. (!g *. a.(k).(i))
        done
      done;
    d.(i) <- a.(i).(i);
    a.(i).(i) <- 1.0;
    for j = 0 to l do
      a.(j).(i) <- 0.0;
      a.(i).(j) <- 0.0
    done
  done

let pythag a b =
  let a = Float.abs a and b = Float.abs b in
  if a > b then a *. sqrt (1.0 +. ((b /. a) *. (b /. a))) else if b = 0.0 then 0.0 else b *. sqrt (1.0 +. ((a /. b) *. (a /. b)))

(* eigenvalues of a symmetric tridiagonal matrix by the implicit QL method,
   accumulating the transformations into z (columns become eigenvectors) *)
let tql2 (d : float array) (e : float array) (z : mat) =
  let n = Array.length d in
  for i = 1 to n - 1 do
    e.(i - 1) <- e.(i)
  done;
  if n > 0 then e.(n - 1) <- 0.0;
  for l = 0 to n - 1 do
    let iter = ref 0 and settled = ref false in
    while not !settled do
      let m = ref l in
      let stop = ref false in
      while (not !stop) && !m < n - 1 do
        let dd = Float.abs d.(!m) +. Float.abs d.(!m + 1) in
        if Float.abs e.(!m) <= epsilon_float *. dd then stop := true else incr m
      done;
      let m = !m in
      if m = l then settled := true
      else begin
        incr iter;
        if !iter > 60 then failwith "Dense.tql2: no convergence";
        let g = (d.(l + 1) -. d.(l)) /. (2.0 *. e.(l)) in
        let r = pythag g 1.0 in
        let g = ref (d.(m) -. d.(l) +. (e.(l) /. (g +. if g >= 0.0 then Float.abs r else -.Float.abs r))) in
        let s = ref 1.0 and c = ref 1.0 and p = ref 0.0 in
        let i = ref (m - 1) and underflow = ref false in
        while (not !underflow) && !i >= l do
          let f = !s *. e.(!i) and b = !c *. e.(!i) in
          let r = pythag f !g in
          e.(!i + 1) <- r;
          if r = 0.0 then begin
            d.(!i + 1) <- d.(!i + 1) -. !p;
            e.(m) <- 0.0;
            underflow := true
          end
          else begin
            s := f /. r;
            c := !g /. r;
            let g' = d.(!i + 1) -. !p in
            let r = ((d.(!i) -. g') *. !s) +. (2.0 *. !c *. b) in
            p := !s *. r;
            d.(!i + 1) <- g' +. !p;
            g := (!c *. r) -. b;
            for k = 0 to n - 1 do
              let zk = z.(k) in
              let f = zk.(!i + 1) in
              zk.(!i + 1) <- (!s *. zk.(!i)) +. (!c *. f);
              zk.(!i) <- (!c *. zk.(!i)) -. (!s *. f)
            done;
            decr i
          end
        done;
        if not !underflow then begin
          d.(l) <- d.(l) -. !p;
          e.(l) <- !g;
          e.(m) <- 0.0
        end
      end
    done
  done

(* eigenvalues and eigenvectors (as the columns of the returned matrix) *)
let eigh (a : mat) : float array * mat =
  let n = Array.length a in
  let z = copy a and d = Array.make n 0.0 and e = Array.make n 0.0 in
  tred2 z d e;
  tql2 d e z;
  (d, z)

(* the nearest positive semidefinite matrix in the Frobenius norm *)
let psd_part (a : mat) : mat =
  let n = Array.length a in
  let d, v = eigh a in
  let out = make n n in
  for k = 0 to n - 1 do
    let lk = d.(k) in
    if lk > 0.0 then
      for i = 0 to n - 1 do
        let vik = v.(i).(k) *. lk in
        if vik <> 0.0 then begin
          let oi = out.(i) in
          for j = 0 to n - 1 do
            oi.(j) <- oi.(j) +. (vik *. v.(j).(k))
          done
        end
      done
  done;
  out

let min_eig (a : mat) = Array.fold_left Float.min infinity (fst (eigh a))
