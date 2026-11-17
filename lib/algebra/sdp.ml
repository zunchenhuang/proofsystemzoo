(* A small feasibility SDP solver: find a symmetric Q ⪰ 0 (nb × nb) and free
   variables h with

     A_Q·svec(Q) + A_h·h = c

   where every entry Q_ab (a ≤ b) appears in exactly one constraint row
   (with coefficient 1 on the diagonal and 2 off it, i.e. 1 and √2 on the
   svec coordinates). This is the shape of a Gram-matrix problem: one row
   per monomial, collecting the entries whose product is that monomial.

   Douglas–Rachford splitting between the affine set (projection by a
   Cholesky factorisation of AAᵀ, computed once) and the cone S₊ × ℝᵏ
   (projection by an eigendecomposition). The answer is floating point; the
   caller rounds it and checks it exactly. *)

type problem = {
  nb : int;
  m : int;
  entry_row : int array array; (* entry_row.(a).(b) for a ≤ b: its constraint row *)
  hcols : (int * float) array array; (* columns of the free variables *)
  c : float array;
}

type solution = { q : Dense.mat; h : float array; residual : float; iterations : int }

let solve ?(deadline = None) ?(max_iter = 20_000) ?(tol = 1e-10) (p : problem) : solution option =
  let nb = p.nb and m = p.m and nh = Array.length p.hcols in
  (* AAᵀ: diagonal from the Gram entries (disjoint rows), plus the free columns *)
  let aat = Dense.make m m in
  for a = 0 to nb - 1 do
    for b = a to nb - 1 do
      let r = p.entry_row.(a).(b) in
      aat.(r).(r) <- aat.(r).(r) +. if a = b then 1.0 else 2.0
    done
  done;
  Array.iter (fun col -> Array.iter (fun (i, u) -> Array.iter (fun (j, v) -> aat.(i).(j) <- aat.(i).(j) +. (u *. v)) col) col) p.hcols;
  let l = Dense.cholesky aat in
  (* y = (Q as a full symmetric matrix, h); the svec inner product is the
     Frobenius one, so Q is kept as a matrix throughout *)
  let apply (q : Dense.mat) (h : float array) =
    let r = Array.make m 0.0 in
    for a = 0 to nb - 1 do
      let qa = q.(a) and ra = p.entry_row.(a) in
      r.(ra.(a)) <- r.(ra.(a)) +. qa.(a);
      for b = a + 1 to nb - 1 do
        r.(ra.(b)) <- r.(ra.(b)) +. (2.0 *. qa.(b))
      done
    done;
    Array.iteri (fun j col -> let hj = h.(j) in if hj <> 0.0 then Array.iter (fun (i, v) -> r.(i) <- r.(i) +. (v *. hj)) col) p.hcols;
    r
  in
  (* P_L: y − Aᵀ(AAᵀ)⁻¹(Ay − c); for a Q entry the svec scaling cancels, so
     both triangles of Q move by t_row *)
  let project_affine (q : Dense.mat) (h : float array) =
    let r = apply q h in
    for i = 0 to m - 1 do
      r.(i) <- r.(i) -. p.c.(i)
    done;
    let t = Dense.chol_solve l r in
    let q' = Dense.copy q in
    for a = 0 to nb - 1 do
      let ra = p.entry_row.(a) in
      q'.(a).(a) <- q'.(a).(a) -. t.(ra.(a));
      for b = a + 1 to nb - 1 do
        let d = t.(ra.(b)) in
        q'.(a).(b) <- q'.(a).(b) -. d;
        q'.(b).(a) <- q'.(b).(a) -. d
      done
    done;
    let h' = Array.mapi (fun j hj -> hj -. Array.fold_left (fun s (i, v) -> s +. (v *. t.(i))) 0.0 p.hcols.(j)) h in
    (q', h')
  in
  let norm2 q h =
    let s = ref 0.0 in
    Array.iter (Array.iter (fun x -> s := !s +. (x *. x))) q;
    Array.iter (fun x -> s := !s +. (x *. x)) h;
    !s
  in
  let yq = ref (Dense.make nb nb) and yh = ref (Array.make nh 0.0) in
  let result = ref None and k = ref 0 and last_gap = ref infinity in
  (try
     while !result = None && !k < max_iter do
       incr k;
       let xq, xh = project_affine !yq !yh in
       let rq = Array.init nb (fun a -> Array.init nb (fun b -> (2.0 *. xq.(a).(b)) -. !yq.(a).(b))) in
       let zq = Dense.psd_part rq in
       let zh = Array.mapi (fun j x -> (2.0 *. x) -. !yh.(j)) xh in
       let dq = Array.init nb (fun a -> Array.init nb (fun b -> zq.(a).(b) -. xq.(a).(b))) and dh = Array.mapi (fun j z -> z -. xh.(j)) zh in
       yq := Array.init nb (fun a -> Array.init nb (fun b -> !yq.(a).(b) +. dq.(a).(b)));
       yh := Array.mapi (fun j y -> y +. dh.(j)) !yh;
       let gap = sqrt (norm2 dq dh) /. (1.0 +. sqrt (norm2 xq xh)) in
       if gap < tol then result := Some { q = zq; h = zh; residual = gap; iterations = !k };
       (* on an infeasible problem the iterates drift by a constant step:
          the gap settles at the distance between the two sets *)
       if !k mod 250 = 0 then begin
         if !k >= 500 && gap > 1e-6 && Float.abs (gap -. !last_gap) < 1e-4 *. gap then raise Exit;
         last_gap := gap
       end;
       if !k land 15 = 0 then Clock.check deadline
     done
   with Clock.Timeout | Exit -> ());
  !result
