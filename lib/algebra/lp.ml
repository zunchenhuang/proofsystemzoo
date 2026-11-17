(* Exact answers to linear-programming questions.

   Cutting Planes, Sherali–Adams and DSOS all ask the same kind of question
   about a large, very degenerate LP: is there y ≥ 0 with A y = b? The
   answer has to be exact, because it becomes (or rules out) a proof.

   The work is split in two. A floating-point revised simplex (phase 1,
   product-form inverse with periodic reinversion, a crash basis of
   singleton columns, a perturbed right-hand side against degeneracy,
   Dantzig pricing, Harris ratio test, Bland's rule when stalled) finds a
   candidate basis. Its suggestions — the basic solution, or the duals when
   the system is infeasible — are then rounded to rationals and checked in
   exact arithmetic. Only checked answers are returned; when rounding does
   not produce one, a budgeted exact fallback is tried, and failing that the
   answer is [Undecided], never a guess. *)

exception Gave_up of string

let debug = Sys.getenv_opt "PSZ_DEBUG" <> None

(* ------------------------------------------------ unboxed growable buffers *)
module Fbuf = struct
  type t = { mutable a : float array; mutable n : int }

  let create k = { a = Array.make (max 16 k) 0.0; n = 0 }
  let clear b = b.n <- 0

  let push b x =
    if b.n = Array.length b.a then begin
      let a = Array.make (2 * b.n) 0.0 in
      Array.blit b.a 0 a 0 b.n;
      b.a <- a
    end;
    Array.unsafe_set b.a b.n x;
    b.n <- b.n + 1
end

module Ibuf = struct
  type t = { mutable a : int array; mutable n : int }

  let create k = { a = Array.make (max 16 k) 0; n = 0 }
  let clear b = b.n <- 0

  let push b x =
    if b.n = Array.length b.a then begin
      let a = Array.make (2 * b.n) 0 in
      Array.blit b.a 0 a 0 b.n;
      b.a <- a
    end;
    Array.unsafe_set b.a b.n x;
    b.n <- b.n + 1
end

(* ------------------------------------------------ the float problem *)

(* A x = b, x ≥ 0, b ≥ 0; columns 0..n-1 are structural, n..n+m-1 the
   artificial unit columns of phase 1 *)
type problem = {
  m : int;
  n : int;
  colptr : int array;
  rowidx : int array;
  vals : float array;
  rowptr : int array;
  colidx : int array;
  rvals : float array;
  b : float array;
}

let make_problem m (cols : (int * float) array array) (b : float array) =
  let n = Array.length cols in
  let nnz = Array.fold_left (fun s c -> s + Array.length c) 0 cols in
  let colptr = Array.make (n + 1) 0 and rowidx = Array.make nnz 0 and vals = Array.make nnz 0.0 in
  let q = ref 0 in
  Array.iteri
    (fun j c ->
      colptr.(j) <- !q;
      Array.iter
        (fun (i, v) ->
          rowidx.(!q) <- i;
          vals.(!q) <- v;
          incr q)
        c)
    cols;
  colptr.(n) <- !q;
  let count = Array.make (m + 1) 0 in
  Array.iter (fun i -> count.(i + 1) <- count.(i + 1) + 1) rowidx;
  for i = 1 to m do
    count.(i) <- count.(i) + count.(i - 1)
  done;
  let rowptr = Array.copy count and fill = Array.copy count in
  let colidx = Array.make nnz 0 and rvals = Array.make nnz 0.0 in
  for j = 0 to n - 1 do
    for q = colptr.(j) to colptr.(j + 1) - 1 do
      let i = rowidx.(q) in
      colidx.(fill.(i)) <- j;
      rvals.(fill.(i)) <- vals.(q);
      fill.(i) <- fill.(i) + 1
    done
  done;
  { m; n; colptr; rowidx; vals; rowptr; colidx; rvals; b }

(* ------------------------------------------------ revised simplex *)

let dtol = 1e-9 (* reduced costs *)
let ptol = 1e-7 (* pivots *)
let ftol = 1e-9 (* primal feasibility, Harris *)
let drop = 1e-13 (* eta entries *)

type state = {
  p : problem;
  rhs : float array; (* perturbed *)
  head : int array; (* basic variable at each position (= pivot row) *)
  pos : int array; (* position of each variable, or -1 *)
  xb : float array;
  d : float array; (* reduced costs, all n + m variables *)
  blocked : bool array;
  wt : float array; (* devex reference weights *)
  er : Ibuf.t; (* eta file: pivot row, start offsets, entries, pivots *)
  es : Ibuf.t;
  ei : Ibuf.t;
  ev : Fbuf.t;
  ep : Fbuf.t;
  mutable w : float;
  mutable w_eps : float; (* perturbation on the initially artificial rows *)
  alpha : float array;
  rho : float array;
  arow : float array;
  mark : bool array;
  touched : Ibuf.t;
}

let neta st = st.er.n

let ftran st (x : float array) =
  let er = st.er.a and es = st.es.a and ei = st.ei.a and ev = st.ev.a and ep = st.ep.a in
  for k = 0 to neta st - 1 do
    let r = Array.unsafe_get er k in
    let xr = Array.unsafe_get x r in
    if xr <> 0.0 then begin
      let t = xr /. Array.unsafe_get ep k in
      for q = Array.unsafe_get es k to Array.unsafe_get es (k + 1) - 1 do
        let i = Array.unsafe_get ei q in
        Array.unsafe_set x i (Array.unsafe_get x i -. (Array.unsafe_get ev q *. t))
      done;
      Array.unsafe_set x r t
    end
  done

let btran st (y : float array) =
  let er = st.er.a and es = st.es.a and ei = st.ei.a and ev = st.ev.a and ep = st.ep.a in
  for k = neta st - 1 downto 0 do
    let r = Array.unsafe_get er k in
    let s = ref (Array.unsafe_get y r) in
    for q = Array.unsafe_get es k to Array.unsafe_get es (k + 1) - 1 do
      s := !s -. (Array.unsafe_get y (Array.unsafe_get ei q) *. Array.unsafe_get ev q)
    done;
    Array.unsafe_set y r (!s /. Array.unsafe_get ep k)
  done

let push_eta st r (x : float array) =
  for i = 0 to st.p.m - 1 do
    let v = Array.unsafe_get x i in
    if i <> r && Float.abs v > drop then begin
      Ibuf.push st.ei i;
      Fbuf.push st.ev v
    end
  done;
  Ibuf.push st.er r;
  Fbuf.push st.ep x.(r);
  Ibuf.push st.es st.ei.n

let clear_etas st =
  Ibuf.clear st.er;
  Ibuf.clear st.es;
  Ibuf.clear st.ei;
  Fbuf.clear st.ev;
  Fbuf.clear st.ep;
  Ibuf.push st.es 0

(* dense copy of column j (structural or artificial) into x *)
let load st j (x : float array) =
  Array.fill x 0 st.p.m 0.0;
  if j < st.p.n then
    for q = st.p.colptr.(j) to st.p.colptr.(j + 1) - 1 do
      let i = st.p.rowidx.(q) in
      x.(i) <- x.(i) +. st.p.vals.(q)
    done
  else x.(j - st.p.n) <- 1.0

let cost st j = if j >= st.p.n then 1.0 else 0.0

(* π = c_B B⁻¹, then d = c − πA; also recomputes w *)
let recompute_duals st =
  let p = st.p in
  let y = Array.init p.m (fun r -> cost st st.head.(r)) in
  btran st y;
  for j = 0 to p.n - 1 do
    let s = ref 0.0 in
    for q = p.colptr.(j) to p.colptr.(j + 1) - 1 do
      s := !s +. (y.(p.rowidx.(q)) *. p.vals.(q))
    done;
    st.d.(j) <- -. !s
  done;
  for i = 0 to p.m - 1 do
    st.d.(p.n + i) <- 1.0 -. y.(i)
  done;
  Array.iter (fun j -> st.d.(j) <- 0.0) st.head;
  st.w <- 0.0;
  Array.iteri (fun r j -> if j >= p.n then st.w <- st.w +. st.xb.(r)) st.head;
  y

(* Rebuild the eta file from the current basis: artificials are identity
   columns, structurals are eliminated in order of increasing length with
   the largest available pivot; a numerically dependent column leaves the
   basis and the artificial of an uncovered row takes its place. *)
let reinvert st =
  let p = st.p in
  clear_etas st;
  let assigned = Array.make p.m false and newhead = Array.make p.m (-1) in
  Array.iter (fun j -> if j >= p.n then begin assigned.(j - p.n) <- true; newhead.(j - p.n) <- j end) st.head;
  let structurals = List.filter (fun j -> j < p.n) (Array.to_list st.head) in
  let len j = p.colptr.(j + 1) - p.colptr.(j) in
  let structurals = List.stable_sort (fun a b -> Int.compare (len a) (len b)) structurals in
  let x = st.alpha in
  List.iter
    (fun j ->
      load st j x;
      ftran st x;
      let best = ref (-1) and bv = ref 0.0 in
      for i = 0 to p.m - 1 do
        if (not assigned.(i)) && Float.abs x.(i) > !bv then begin
          bv := Float.abs x.(i);
          best := i
        end
      done;
      if !best >= 0 && !bv > 1e-9 then begin
        push_eta st !best x;
        assigned.(!best) <- true;
        newhead.(!best) <- j
      end)
    structurals;
  Array.fill st.pos 0 (Array.length st.pos) (-1);
  for i = 0 to p.m - 1 do
    if newhead.(i) < 0 then newhead.(i) <- p.n + i;
    st.head.(i) <- newhead.(i);
    st.pos.(newhead.(i)) <- i
  done;
  Array.blit st.rhs 0 st.xb 0 p.m;
  ftran st st.xb;
  Array.iteri (fun i v -> if v < 0.0 && v > -1e-7 then st.xb.(i) <- 0.0) st.xb;
  ignore (recompute_duals st)

(* singleton columns as a crash basis: a row whose right-hand side is 0 can
   start with a structural column that has its only entry there *)
let init (p : problem) =
  let nv = p.n + p.m in
  let st =
    {
      p;
      rhs = Array.copy p.b;
      head = Array.init p.m (fun i -> p.n + i);
      pos = Array.init nv (fun j -> if j >= p.n then j - p.n else -1);
      xb = Array.make p.m 0.0;
      d = Array.make nv 0.0;
      blocked = Array.make nv false;
      wt = Array.make nv 1.0;
      er = Ibuf.create 64;
      es = Ibuf.create 64;
      ei = Ibuf.create 1024;
      ev = Fbuf.create 1024;
      ep = Fbuf.create 64;
      w = 0.0;
      w_eps = 0.0;
      alpha = Array.make p.m 0.0;
      rho = Array.make p.m 0.0;
      arow = Array.make nv 0.0;
      mark = Array.make nv false;
      touched = Ibuf.create 1024;
    }
  in
  clear_etas st;
  let crash = Array.make p.m (-1) in
  for j = 0 to p.n - 1 do
    if p.colptr.(j + 1) - p.colptr.(j) = 1 then begin
      let q = p.colptr.(j) in
      let i = p.rowidx.(q) in
      if p.b.(i) = 0.0 && Float.abs p.vals.(q) >= 1e-3 && crash.(i) < 0 then crash.(i) <- j
    end
  done;
  (* distinct tiny shifts break the degeneracy. The shifted right-hand side
     is b + [A I]·δ with δ ≥ 0 (δ on the crash columns and the artificials),
     so a feasible problem stays feasible with phase-1 value at most the
     shift on the artificial rows; answers are re-derived from the true b *)
  for i = 0 to p.m - 1 do
    let eps = 1e-6 *. (1.0 +. (float_of_int ((i * 7919) mod (p.m + 1)) /. float_of_int (p.m + 1))) in
    let j = crash.(i) in
    if j >= 0 then begin
      let v = p.vals.(p.colptr.(j)) in
      st.rhs.(i) <- eps *. v;
      st.pos.(p.n + i) <- -1;
      st.head.(i) <- j;
      st.pos.(j) <- i;
      Ibuf.push st.er i;
      Fbuf.push st.ep v;
      Ibuf.push st.es st.ei.n
    end
    else begin
      st.rhs.(i) <- p.b.(i) +. eps;
      st.w_eps <- st.w_eps +. eps
    end
  done;
  Array.blit st.rhs 0 st.xb 0 p.m;
  ftran st st.xb;
  ignore (recompute_duals st);
  st

(* entering variable: largest d_j²/w_j (devex), or (Bland) the first
   improving one *)
let choose st bland =
  let best = ref (-1) and bd = ref 0.0 in
  let nv = Array.length st.d in
  if bland then begin
    let j = ref 0 in
    while !best < 0 && !j < nv do
      if st.d.(!j) < -.dtol && st.pos.(!j) < 0 && not st.blocked.(!j) then best := !j;
      incr j
    done
  end
  else
    for j = 0 to nv - 1 do
      let dj = Array.unsafe_get st.d j in
      if dj < -.dtol && st.pos.(j) < 0 && not st.blocked.(j) then begin
        let score = dj *. dj /. Array.unsafe_get st.wt j in
        if score > !bd then begin
          bd := score;
          best := j
        end
      end
    done;
  !best

(* leaving row: Harris two-pass (largest pivot among near-minimal ratios),
   or the minimum ratio with Bland's tie-break *)
let ratio st bland =
  let a = st.alpha and x = st.xb and m = st.p.m in
  let leave = ref (-1) in
  if not bland then begin
    let theta = ref infinity in
    for i = 0 to m - 1 do
      let c = a.(i) in
      if c > ptol then begin
        let r = (x.(i) +. ftol) /. c in
        if r < !theta then theta := r
      end
    done;
    let bc = ref 0.0 in
    for i = 0 to m - 1 do
      let c = a.(i) in
      if c > ptol && x.(i) /. c <= !theta then
        if c > !bc || (c = !bc && !leave >= 0 && st.head.(i) < st.head.(!leave)) then begin
          bc := c;
          leave := i
        end
    done
  end
  else begin
    let br = ref infinity in
    for i = 0 to m - 1 do
      let c = a.(i) in
      if c > ptol then begin
        let r = x.(i) /. c in
        if r < !br || (r = !br && !leave >= 0 && st.head.(i) < st.head.(!leave)) then begin
          br := r;
          leave := i
        end
      end
    done
  end;
  !leave

let pivot st e r =
  let p = st.p in
  let are = st.alpha.(r) in
  let de = st.d.(e) in
  let rho = st.rho in
  Array.fill rho 0 p.m 0.0;
  rho.(r) <- 1.0;
  btran st rho;
  (* row r of the tableau, through the row-wise copy of A *)
  Ibuf.clear st.touched;
  for i = 0 to p.m - 1 do
    let ri = rho.(i) in
    if ri <> 0.0 then
      for q = p.rowptr.(i) to p.rowptr.(i + 1) - 1 do
        let j = Array.unsafe_get p.colidx q in
        if not (Array.unsafe_get st.mark j) then begin
          Array.unsafe_set st.mark j true;
          Ibuf.push st.touched j
        end;
        Array.unsafe_set st.arow j (Array.unsafe_get st.arow j +. (ri *. Array.unsafe_get p.rvals q))
      done
  done;
  let f = de /. are in
  let we = st.wt.(e) in
  let devex j a =
    if st.pos.(j) < 0 && j <> e then begin
      let ratio = a /. are in
      let v = ratio *. ratio *. we in
      if v > st.wt.(j) then st.wt.(j) <- v
    end
  in
  for t = 0 to st.touched.n - 1 do
    let j = st.touched.a.(t) in
    let a = st.arow.(j) in
    st.d.(j) <- st.d.(j) -. (f *. a);
    devex j a;
    st.arow.(j) <- 0.0;
    st.mark.(j) <- false
  done;
  for i = 0 to p.m - 1 do
    let ri = rho.(i) in
    if ri <> 0.0 then begin
      st.d.(p.n + i) <- st.d.(p.n + i) -. (f *. ri);
      devex (p.n + i) ri
    end
  done;
  let lv = st.head.(r) in
  st.wt.(lv) <- Float.max (we /. (are *. are)) 1.0;
  if st.wt.(lv) > 1e12 then Array.fill st.wt 0 (Array.length st.wt) 1.0;
  Array.iter (fun j -> st.d.(j) <- 0.0) st.head;
  st.d.(lv) <- -.f;
  let theta = st.xb.(r) /. are in
  for i = 0 to p.m - 1 do
    let a = st.alpha.(i) in
    if a <> 0.0 then st.xb.(i) <- st.xb.(i) -. (theta *. a)
  done;
  st.xb.(r) <- theta;
  st.w <- st.w +. (de *. theta);
  push_eta st r st.alpha;
  st.head.(r) <- e;
  st.pos.(e) <- r;
  st.pos.(lv) <- -1;
  st.d.(e) <- 0.0

(* Phase 1 to optimality (for the perturbed problem). Raises [Gave_up] when
   floating point breaks down, [Clock.Timeout] at the deadline. *)
let phase1 ?(deadline = None) (p : problem) : state =
  let st = init p in
  let limit = (20 * (p.m + p.n)) + 1000 in
  let pivots = ref 0 and stall = ref 0 and since = ref 0 in
  let scale = 1e-12 *. (1.0 +. Array.fold_left ( +. ) 0.0 p.b) in
  let finished = ref false in
  while not !finished do
    if st.w <= scale then finished := true
    else begin
      let bland = !stall >= 300 in
      let e = choose st bland in
      if e < 0 then finished := true
      else begin
        load st e st.alpha;
        ftran st st.alpha;
        let r = ratio st bland in
        if r < 0 then st.blocked.(e) <- true
        else begin
          let w0 = st.w in
          pivot st e r;
          incr pivots;
          incr since;
          stall := if w0 -. st.w > 1e-13 *. (1.0 +. w0) then 0 else !stall + 1;
          if not (Float.is_finite st.w) then raise (Gave_up "floating-point breakdown");
          if !pivots > limit then raise (Gave_up (Printf.sprintf "more than %d simplex pivots" limit));
          if debug && st.w < -1e-6 then Printf.eprintf "[lp]   negative w=%g at pivot %d\n%!" st.w !pivots;
          if !since >= 64 || neta st > 2 * p.m + 64 then begin
            reinvert st;
            since := 0
          end;
          if debug && !pivots mod 1000 = 0 then begin
            let arts = Array.fold_left (fun c j -> if j >= p.n then c + 1 else c) 0 st.head in
            let negs = Array.fold_left (fun c x -> if x < -1e-9 then c + 1 else c) 0 st.xb in
            let mx = Array.fold_left Float.max 0.0 st.xb in
            Printf.eprintf "[lp]   pivot %d w=%.12g stall=%d arts=%d neg=%d maxx=%g etas=%d nnz=%d\n%!" !pivots st.w !stall arts negs mx (neta st) st.ei.n
          end;
          if !pivots land 31 = 0 then Clock.check deadline
        end
      end
    end
  done;
  reinvert st;
  if debug then Printf.eprintf "[lp] %d x %d: %d pivots, w=%.3g, etas=%d (%d nnz)\n%!" p.m p.n !pivots st.w (neta st) st.ei.n;
  st

(* the basic solution for the true right-hand side *)
let basic_solution st : (int * float) list =
  let x = Array.copy st.p.b in
  ftran st x;
  Array.to_list (Array.mapi (fun r j -> (j, x.(r))) st.head) |> List.filter (fun (j, _) -> j < st.p.n)

let duals st = Array.init st.p.m (fun i -> 1.0 -. st.d.(st.p.n + i))

(* ------------------------------------------------ exact layer *)

let maxdens = [ 1_000; 1_000_000; 1_000_000_000 ]

let rationalize_with den (v : float) = if Float.abs v < 1e-11 then Q.zero else Num.rationalize ~maxden:(Z.of_int den) v

(* exact y ≥ 0 on [support] with Σ y_j·col_j = rhs, by elimination in ℚ
   on the rows the support touches; None if inconsistent, negative or over
   budget *)
let solve_support ~budget (cols : (int * Q.t) array array) (support : int list) (rhs : (int * Q.t) list) =
  let s = Array.of_list (List.sort_uniq compare support) in
  let rows = Hashtbl.create 64 in
  let row i = match Hashtbl.find_opt rows i with Some k -> k | None -> let k = Hashtbl.length rows in Hashtbl.replace rows i k; k in
  Array.iter (fun j -> Array.iter (fun (i, _) -> ignore (row i)) cols.(j)) s;
  List.iter (fun (i, _) -> ignore (row i)) rhs;
  let nr = Hashtbl.length rows and ns = Array.length s in
  if nr * (ns + 1) > budget then None
  else begin
    let a = Array.init nr (fun _ -> Array.make (ns + 1) Q.zero) in
    Array.iteri (fun c j -> Array.iter (fun (i, v) -> let k = row i in a.(k).(c) <- Q.add a.(k).(c) v) cols.(j)) s;
    List.iter (fun (i, v) -> let k = row i in a.(k).(ns) <- v) rhs;
    let piv = ref [] and r = ref 0 in
    for c = 0 to ns - 1 do
      if !r < nr then begin
        let p = ref (-1) in
        for i = !r to nr - 1 do
          if !p < 0 && Q.sign a.(i).(c) <> 0 then p := i
        done;
        if !p >= 0 then begin
          let tmp = a.(!r) in
          a.(!r) <- a.(!p);
          a.(!p) <- tmp;
          let inv = Q.inv a.(!r).(c) in
          a.(!r) <- Array.map (fun x -> Q.mul x inv) a.(!r);
          for i = 0 to nr - 1 do
            if i <> !r && Q.sign a.(i).(c) <> 0 then begin
              let f = a.(i).(c) in
              let ar = a.(!r) in
              a.(i) <- Array.mapi (fun k x -> if Q.sign ar.(k) = 0 then x else Q.sub x (Q.mul f ar.(k))) a.(i)
            end
          done;
          piv := (!r, c) :: !piv;
          incr r
        end
      end
    done;
    let consistent = ref true in
    for i = !r to nr - 1 do
      if Q.sign a.(i).(ns) <> 0 then consistent := false
    done;
    if not !consistent then None
    else
      let y = List.map (fun (i, c) -> (s.(c), a.(i).(ns))) !piv in
      if List.for_all (fun (_, v) -> Q.sign v >= 0) y then Some y else None
  end

(* A small dense exact simplex (Bland's rule, phase 1): y ≥ 0 with
   A y = rhs, for problems too small to be worth anything cleverer, and as
   the last resort when floating point fails on one. *)
let exact_phase1 ~deadline m (cols : (int * Q.t) array array) (rhs : Q.t array) : (int * Q.t) list option =
  let n = Array.length cols in
  let sign = Array.map (fun r -> if Q.sign r < 0 then Q.minus_one else Q.one) rhs in
  let nc = n + m in
  let t = Array.init m (fun _ -> Array.make (nc + 1) Q.zero) in
  Array.iteri (fun j c -> Array.iter (fun (i, v) -> t.(i).(j) <- Q.add t.(i).(j) (Q.mul sign.(i) v)) c) cols;
  for i = 0 to m - 1 do
    t.(i).(n + i) <- Q.one;
    t.(i).(nc) <- Q.mul sign.(i) rhs.(i)
  done;
  let basis = Array.init m (fun i -> n + i) in
  let obj = Array.make (nc + 1) Q.zero in
  for i = 0 to m - 1 do
    for j = 0 to n - 1 do
      obj.(j) <- Q.sub obj.(j) t.(i).(j)
    done;
    obj.(nc) <- Q.sub obj.(nc) t.(i).(nc)
  done;
  let steps = ref 0 in
  let rec loop () =
    incr steps;
    if !steps land 15 = 0 then Clock.check deadline;
    let e = ref (-1) in
    for j = nc - 1 downto 0 do
      if Q.sign obj.(j) < 0 then e := j
    done;
    if !e >= 0 then begin
      let e = !e in
      let l = ref (-1) and br = ref Q.zero in
      for i = 0 to m - 1 do
        if Q.sign t.(i).(e) > 0 then begin
          let r = Q.div t.(i).(nc) t.(i).(e) in
          if !l < 0 || Q.lt r !br || (Q.equal r !br && basis.(i) < basis.(!l)) then begin
            l := i;
            br := r
          end
        end
      done;
      if !l >= 0 then begin
        let l = !l in
        let inv = Q.inv t.(l).(e) in
        t.(l) <- Array.map (fun x -> Q.mul x inv) t.(l);
        let elim row =
          let f = row.(e) in
          if Q.sign f = 0 then row else Array.mapi (fun k x -> Q.sub x (Q.mul f t.(l).(k))) row
        in
        for i = 0 to m - 1 do
          if i <> l then t.(i) <- elim t.(i)
        done;
        let o = elim obj in
        Array.blit o 0 obj 0 (nc + 1);
        basis.(l) <- e;
        loop ()
      end
    end
  in
  loop ();
  if Q.sign obj.(nc) <> 0 then None
  else Some (List.filter_map (fun i -> if basis.(i) < n && Q.sign t.(i).(nc) > 0 then Some (basis.(i), t.(i).(nc)) else None) (List.init m Fun.id))

let small m n = m * (n + m) <= 60_000

(* ------------------------------------------------ Farkas *)

type farkas =
  | Certificate of Q.t array (* y ≥ 0 per row, Σ yᵢaᵢ = 0 and Σ yᵢbᵢ > 0: exactly checked *)
  | Point of Q.t array (* z satisfying every row: exactly checked *)
  | Undecided of string

(* Rows Σ_v a_v·z_v ≥ b over variables 0..nvars-1. Either a nonnegative
   combination of the rows reads 0 ≥ positive (a certificate that the system
   has no solution), or a point satisfies all of them. *)
let farkas ?(deadline = None) ~nvars (rows : ((int * Q.t) array * Q.t) array) : farkas =
  let k = Array.length rows in
  let m = nvars + 1 in
  let qcols = Array.map (fun (a, b) -> Array.append (Array.of_list (List.filter (fun (_, c) -> Q.sign c <> 0) (Array.to_list a))) (if Q.sign b <> 0 then [| (nvars, b) |] else [||])) rows in
  let check_cert (y : Q.t array) =
    let acc = Array.make m Q.zero in
    Array.iteri (fun j v -> if Q.sign v <> 0 then Array.iter (fun (i, c) -> acc.(i) <- Q.add acc.(i) (Q.mul v c)) qcols.(j)) y;
    Array.for_all (fun v -> Q.sign v >= 0) y && Q.sign acc.(nvars) > 0 && Array.for_all (fun v -> Q.sign v = 0) (Array.sub acc 0 nvars)
  in
  let check_point (z : Q.t array) =
    Array.for_all (fun (a, b) -> Q.geq (Array.fold_left (fun s (v, c) -> Q.add s (Q.mul c z.(v))) Q.zero a) b) rows
  in
  let exact () =
    if small m k then
      match exact_phase1 ~deadline m qcols (Array.init m (fun i -> if i = nvars then Q.one else Q.zero)) with
      | Some y ->
          let a = Array.make k Q.zero in
          List.iter (fun (j, v) -> a.(j) <- v) y;
          if check_cert a then Certificate a else Undecided "exact simplex: certificate check failed"
      | None -> Undecided "no certificate (exact simplex), but no point was extracted"
    else Undecided "floating-point answer could not be certified"
  in
  let fcols = Array.map (Array.map (fun (i, c) -> (i, Q.to_float c))) qcols in
  match phase1 ~deadline (make_problem m fcols (Array.init m (fun i -> if i = nvars then 1.0 else 0.0))) with
  | exception Gave_up _ -> exact ()
  | st -> (
      let try_cert () =
        let sol = basic_solution st in
        let support = List.filter_map (fun (j, v) -> if v > 1e-11 then Some j else None) sol in
        let from_den den =
          let y = Array.make k Q.zero in
          List.iter (fun (j, v) -> y.(j) <- rationalize_with den v) sol;
          if check_cert y then Some y else None
        in
        match List.find_map from_den maxdens with
        | Some y -> Some y
        | None -> (
            match solve_support ~budget:400_000 qcols support [ (nvars, Q.one) ] with
            | Some y ->
                let a = Array.make k Q.zero in
                List.iter (fun (j, v) -> a.(j) <- v) y;
                if check_cert a then Some a else None
            | None -> None)
      in
      let try_point () =
        let pi = duals st in
        let last = pi.(nvars) in
        if last <= 1e-9 then None
        else
          List.find_map
            (fun den ->
              let z = Array.init nvars (fun v -> rationalize_with den (-.pi.(v) /. last)) in
              if check_point z then Some z else None)
            [ 1_000; 1_000_000 ]
      in
      let feasible = st.w <= st.w_eps +. 1e-7 in
      match if feasible then Option.map (fun y -> Certificate y) (try_cert ()) else None with
      | Some c -> c
      | None -> (
          match try_point () with
          | Some z -> Point z
          | None -> ( match if feasible then None else try_cert () with Some y -> Certificate y | None -> exact ())))

(* ------------------------------------------------ y ≥ 0, A y = rhs *)

type solve =
  | Solution of (int * Q.t) list (* exactly checked *)
  | No_solution (* the floating-point verdict, not certified *)
  | Unknown of string

let nonneg ?(deadline = None) ~m (cols : (int * Q.t) array array) (rhs : Q.t array) : solve =
  let k = Array.length cols in
  let sign = Array.map (fun r -> if Q.sign r < 0 then Q.minus_one else Q.one) rhs in
  let cols = Array.map (Array.map (fun (i, c) -> (i, Q.mul sign.(i) c))) cols in
  let r = Array.mapi (fun i x -> Q.mul sign.(i) x) rhs in
  let check y =
    let acc = Array.make m Q.zero in
    List.for_all (fun (_, v) -> Q.sign v >= 0) y
    && begin
         List.iter (fun (j, v) -> Array.iter (fun (i, c) -> acc.(i) <- Q.add acc.(i) (Q.mul v c)) cols.(j)) y;
         Array.for_all2 Q.equal acc r
       end
  in
  let exact () =
    if small m k then
      match exact_phase1 ~deadline m cols r with
      | Some y when check y -> Solution y
      | Some _ -> Unknown "exact simplex: solution check failed"
      | None -> No_solution
    else Unknown "floating-point answer could not be certified"
  in
  let fcols = Array.map (Array.map (fun (i, c) -> (i, Q.to_float c))) cols in
  match phase1 ~deadline (make_problem m fcols (Array.map Q.to_float r)) with
  | exception Gave_up _ -> exact ()
  | st -> (
      (* the final basis is tried against the true right-hand side first;
         only a phase-1 value beyond the perturbation means "no solution" *)
      let sol = basic_solution st in
      let of_den den = List.filter_map (fun (j, v) -> let q = rationalize_with den v in if Q.sign q = 0 then None else Some (j, q)) sol in
      match List.find_opt check (List.map of_den maxdens) with
      | Some y -> Solution y
      | None -> (
          let support = List.filter_map (fun (j, v) -> if v > 1e-11 then Some j else None) sol in
          match solve_support ~budget:400_000 cols support (List.filter (fun (_, v) -> Q.sign v <> 0) (List.mapi (fun i v -> (i, v)) (Array.to_list r))) with
          | Some y when check y -> Solution y
          | _ -> if st.w > st.w_eps +. 1e-7 then No_solution else exact ()))
