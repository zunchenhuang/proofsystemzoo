(* DRAT clausal proofs: a CDCL solver that logs its learnt clauses (each a
   RUP lemma), a forward checker (RUP, or RAT on the first literal), and a
   parser for textual DRAT. Proof format drat/1. *)
open System

let format = "drat/1"

(* literal order matters for RAT (the pivot is the first literal), so steps
   keep the literals as given *)
type step = Add of int array | Delete of int array
type proof = step list

let step_codec : step Json.codec =
  let open Json in
  let encode = function Add c -> `List [ `String "a"; E.array E.int c ] | Delete c -> `List [ `String "d"; E.array E.int c ] in
  let decode j =
    let* k, lits = D.pair D.string (D.array D.int) j in
    match k with "a" -> Ok (Add lits) | "d" -> Ok (Delete lits) | k -> error "unknown step kind %S" k
  in
  codec encode decode

let codec : proof Json.codec =
  let open Json in
  codec
    (fun steps -> E.obj [ ("format", `String format); ("steps", E.list step_codec.encode steps) ])
    (fun j ->
      let* () = D.tag "format" format j in
      D.field "steps" (D.list step_codec.decode) j)

(* textual DRAT: one clause per line, terminated by 0, "d" for deletions *)
let parse_drat (text : string) : (proof, string) result =
  let line raw =
    match List.filter (( <> ) "") (String.split_on_char ' ' (String.trim (String.map (fun c -> if c = '\t' then ' ' else c) raw))) with
    | [] | "c" :: _ -> Ok None
    | toks -> (
        let del, toks = match toks with "d" :: r -> (true, r) | r -> (false, r) in
        match Seqx.map_result (fun t -> match int_of_string_opt t with Some i -> Ok i | None -> Error ("bad literal " ^ t)) toks with
        | Error e -> Error e
        | Ok lits ->
            let lits = match List.rev lits with 0 :: r -> List.rev r | _ -> lits in
            let c = Array.of_list lits in
            Ok (Some (if del then Delete c else Add c)))
  in
  Result.map (List.filter_map Fun.id) (Seqx.map_result line (String.split_on_char '\n' text))

(* ======================================================== CDCL *)
exception Stop of string

type solver = {
  n : int;
  assign : int array; (* 1 true, -1 false, 0 unassigned *)
  level : int array;
  reason : int array; (* clause index; -1 for decisions and units *)
  activity : float array;
  phase : int array;
  mutable inc : float;
  trail : int Vec.t;
  lim : int Vec.t;
  mutable qhead : int;
  clauses : int array Vec.t;
  watches : int list array; (* by literal code *)
  lemmas : int list Vec.t;
  mutable conflicts : int;
  seen : bool array;
}

let code l = if l > 0 then 2 * l else (2 * -l) + 1
let value s l = if l > 0 then s.assign.(l) else -s.assign.(-l)
let dlevel s = Vec.length s.lim

let enqueue s l r =
  let v = abs l in
  s.assign.(v) <- (if l > 0 then 1 else -1);
  s.level.(v) <- dlevel s;
  s.reason.(v) <- r;
  ignore (Vec.push s.trail l)

let attach s (c : int array) =
  let k = Vec.push s.clauses c in
  s.watches.(code c.(0)) <- k :: s.watches.(code c.(0));
  s.watches.(code c.(1)) <- k :: s.watches.(code c.(1));
  k

let propagate s =
  let confl = ref (-1) in
  while !confl < 0 && s.qhead < Vec.length s.trail do
    let fl = -Vec.get s.trail s.qhead in
    s.qhead <- s.qhead + 1;
    let pending = ref s.watches.(code fl) and keep = ref [] in
    s.watches.(code fl) <- [];
    while !pending <> [] do
      let k = List.hd !pending in
      pending := List.tl !pending;
      if !confl >= 0 then keep := k :: !keep
      else begin
        let c = Vec.get s.clauses k in
        if c.(0) = fl then begin
          c.(0) <- c.(1);
          c.(1) <- fl
        end;
        if value s c.(0) = 1 then keep := k :: !keep
        else begin
          let moved = ref false and j = ref 2 in
          while (not !moved) && !j < Array.length c do
            if value s c.(!j) <> -1 then begin
              let t = c.(1) in
              c.(1) <- c.(!j);
              c.(!j) <- t;
              s.watches.(code c.(1)) <- k :: s.watches.(code c.(1));
              moved := true
            end;
            incr j
          done;
          if not !moved then begin
            keep := k :: !keep;
            if value s c.(0) = -1 then confl := k else enqueue s c.(0) k
          end
        end
      end
    done;
    s.watches.(code fl) <- List.rev_append !keep s.watches.(code fl)
  done;
  !confl

(* first-UIP learning; the literal of highest level among the rest goes second *)
let analyze s confl =
  let learnt = ref [] and counter = ref 0 and p = ref 0 and touched = ref [] in
  let cur = dlevel s in
  let ti = ref (Vec.length s.trail - 1) and confl = ref confl and continue = ref true in
  while !continue do
    Array.iter
      (fun q ->
        if q <> !p then begin
          let v = abs q in
          if (not s.seen.(v)) && s.level.(v) > 0 then begin
            s.seen.(v) <- true;
            touched := v :: !touched;
            s.activity.(v) <- s.activity.(v) +. s.inc;
            if s.level.(v) = cur then incr counter else learnt := q :: !learnt
          end
        end)
      (Vec.get s.clauses !confl);
    while not s.seen.(abs (Vec.get s.trail !ti)) do decr ti done;
    p := Vec.get s.trail !ti;
    decr ti;
    s.seen.(abs !p) <- false;
    decr counter;
    if !counter = 0 then continue := false else confl := s.reason.(abs !p)
  done;
  List.iter (fun v -> s.seen.(v) <- false) !touched;
  let rest = List.rev !learnt in
  let rest =
    match rest with
    | [] -> []
    | h :: _ ->
        let best = List.fold_left (fun b q -> if s.level.(abs q) > s.level.(abs b) then q else b) h rest in
        best :: List.filter (( <> ) best) rest
  in
  let bt = match rest with [] -> 0 | q :: _ -> s.level.(abs q) in
  s.inc <- s.inc *. 1.05;
  if s.inc > 1e100 then begin
    Array.iteri (fun i a -> s.activity.(i) <- a *. 1e-100) s.activity;
    s.inc <- s.inc *. 1e-100
  end;
  (-(!p) :: rest, bt)

let backtrack s lvl =
  if dlevel s > lvl then begin
    let start = Vec.get s.lim lvl in
    for i = start to Vec.length s.trail - 1 do
      let l = Vec.get s.trail i in
      let v = abs l in
      s.phase.(v) <- (if l > 0 then 1 else -1);
      s.assign.(v) <- 0;
      s.reason.(v) <- -1
    done;
    Vec.truncate s.trail start;
    Vec.truncate s.lim lvl;
    s.qhead <- start
  end

(* VSIDS decisions (highest activity, saved phase), restarts never *)
let solve ~deadline ~max_conflicts (cnf : Cnf.t) =
  let n = cnf.num_vars in
  let s =
    {
      n;
      assign = Array.make (n + 1) 0;
      level = Array.make (n + 1) 0;
      reason = Array.make (n + 1) (-1);
      activity = Array.make (n + 1) 0.0;
      phase = Array.make (n + 1) (-1);
      inc = 1.0;
      trail = Vec.create 0;
      lim = Vec.create 0;
      qhead = 0;
      clauses = Vec.create [||];
      watches = Array.make ((2 * n) + 2) [];
      lemmas = Vec.create [];
      conflicts = 0;
      seen = Array.make (n + 1) false;
    }
  in
  let unsat () =
    ignore (Vec.push s.lemmas []);
    (s, false)
  in
  let rec init i =
    if i = Array.length cnf.clauses then None
    else
      match Clause.lits cnf.clauses.(i) with
      | [] -> Some (unsat ())
      | [ l ] ->
          if value s l = -1 then Some (unsat ())
          else begin
            if value s l = 0 then enqueue s l (-1);
            init (i + 1)
          end
      | c ->
          ignore (attach s (Array.of_list c));
          init (i + 1)
  in
  match init 0 with
  | Some r -> r
  | None ->
      let rec loop () =
        let confl = propagate s in
        if confl >= 0 then begin
          s.conflicts <- s.conflicts + 1;
          if dlevel s = 0 then unsat ()
          else begin
            if s.conflicts > max_conflicts then raise (Stop (Printf.sprintf "more than %d conflicts" max_conflicts));
            if s.conflicts land 255 = 0 then Clock.check deadline;
            let learnt, bt = analyze s confl in
            ignore (Vec.push s.lemmas learnt);
            backtrack s bt;
            (match learnt with [ l ] -> enqueue s l (-1) | l :: _ -> enqueue s l (attach s (Array.of_list learnt)) | [] -> ());
            loop ()
          end
        end
        else begin
          let best = ref (-1.0) and vb = ref 0 in
          for v = 1 to n do
            if s.assign.(v) = 0 && s.activity.(v) > !best then begin
              best := s.activity.(v);
              vb := v
            end
          done;
          if !vb = 0 then (s, true)
          else begin
            ignore (Vec.push s.lim (Vec.length s.trail));
            enqueue s (!vb * s.phase.(!vb)) (-1);
            loop ()
          end
        end
      in
      loop ()

(* ===================================================== checker *)
type db = {
  cl : int array Vec.t;
  alive : bool Vec.t;
  dwatch : (int, int list ref) Hashtbl.t;
  units : (int, int) Hashtbl.t; (* clause id -> its literal *)
  mutable empty : int;
  by_key : (int list, int list ref) Hashtbl.t;
  occ : (int, (int, unit) Hashtbl.t) Hashtbl.t;
  mutable vals : int array; (* by variable, during one RUP check *)
}

let dwatch db l =
  match Hashtbl.find_opt db.dwatch l with
  | Some r -> r
  | None ->
      let r = ref [] in
      Hashtbl.replace db.dwatch l r;
      r

let db_add db (lits : int array) =
  let c = Array.of_list (List.rev (Array.fold_left (fun acc l -> if List.mem l acc then acc else l :: acc) [] lits)) in
  let k = Vec.push db.cl c in
  ignore (Vec.push db.alive true);
  let key = List.sort compare (Array.to_list c) in
  (match Hashtbl.find_opt db.by_key key with Some r -> r := k :: !r | None -> Hashtbl.replace db.by_key key (ref [ k ]));
  Array.iter
    (fun l ->
      let h =
        match Hashtbl.find_opt db.occ l with
        | Some h -> h
        | None ->
            let h = Hashtbl.create 8 in
            Hashtbl.replace db.occ l h;
            h
      in
      Hashtbl.replace h k ())
    c;
  match Array.length c with
  | 0 -> db.empty <- db.empty + 1
  | 1 -> Hashtbl.replace db.units k c.(0)
  | _ ->
      let w0 = dwatch db c.(0) and w1 = dwatch db c.(1) in
      w0 := k :: !w0;
      w1 := k :: !w1

let db_delete db (lits : int array) =
  match Hashtbl.find_opt db.by_key (List.sort_uniq compare (Array.to_list lits)) with
  | None -> ()
  | Some ids ->
      let rec go = function
        | [] -> []
        | k :: rest when Vec.get db.alive k ->
            Vec.set db.alive k false;
            Array.iter (fun l -> match Hashtbl.find_opt db.occ l with Some h -> Hashtbl.remove h k | None -> ()) (Vec.get db.cl k);
            Hashtbl.remove db.units k;
            if Array.length (Vec.get db.cl k) = 0 then db.empty <- db.empty - 1;
            rest
        | k :: rest -> k :: go rest
      in
      ids := go !ids

(* reverse unit propagation: assuming the clause false, does unit
   propagation over the live clauses reach a conflict? *)
let rup db (lits : int list) =
  db.empty > 0
  ||
  let queue = Vec.create 0 in
  let ensure v =
    if v >= Array.length db.vals then begin
      let a = Array.make (2 * (v + 1)) 0 in
      Array.blit db.vals 0 a 0 (Array.length db.vals);
      db.vals <- a
    end
  in
  let set_true l =
    let v = abs l and b = if l > 0 then 1 else -1 in
    ensure v;
    match db.vals.(v) with
    | 0 ->
        db.vals.(v) <- b;
        ignore (Vec.push queue l);
        true
    | x -> x = b
  in
  let value l =
    let v = abs l in
    if v >= Array.length db.vals then 0 else if l > 0 then db.vals.(v) else -db.vals.(v)
  in
  let conflict = ref false in
  List.iter (fun l -> if (not !conflict) && not (set_true (-l)) then conflict := true) lits;
  Hashtbl.iter (fun _ u -> if (not !conflict) && not (set_true u) then conflict := true) db.units;
  let qh = ref 0 in
  while (not !conflict) && !qh < Vec.length queue do
    let fl = -Vec.get queue !qh in
    incr qh;
    match Hashtbl.find_opt db.dwatch fl with
    | None -> ()
    | Some ws ->
        let pending = ref !ws and keep = ref [] in
        ws := [];
        while !pending <> [] do
          let k = List.hd !pending in
          pending := List.tl !pending;
          if not (Vec.get db.alive k) then ()
          else if !conflict then keep := k :: !keep
          else begin
            let c = Vec.get db.cl k in
            if c.(0) = fl then begin
              c.(0) <- c.(1);
              c.(1) <- fl
            end;
            if value c.(0) = 1 then keep := k :: !keep
            else begin
              let moved = ref false and j = ref 2 in
              while (not !moved) && !j < Array.length c do
                if value c.(!j) <> -1 then begin
                  let t = c.(1) in
                  c.(1) <- c.(!j);
                  c.(!j) <- t;
                  let w = dwatch db c.(1) in
                  w := k :: !w;
                  moved := true
                end;
                incr j
              done;
              if not !moved then begin
                keep := k :: !keep;
                if value c.(0) = -1 then conflict := true else ignore (set_true c.(0))
              end
            end
          end
        done;
        ws := List.rev_append !keep !ws
  done;
  Vec.iteri (fun _ l -> db.vals.(abs l) <- 0) queue;
  !conflict

(* resolution asymmetric tautology on the first literal *)
let rat db (lits : int list) =
  match lits with
  | [] -> false
  | p :: _ ->
      let cands = match Hashtbl.find_opt db.occ (-p) with None -> [] | Some h -> Hashtbl.fold (fun k () acc -> k :: acc) h [] in
      List.for_all
        (fun k ->
          let res = lits @ List.filter (( <> ) (-p)) (Array.to_list (Vec.get db.cl k)) in
          List.exists (fun l -> List.mem (-l) res) res || rup db res)
        cands

let measures (steps : proof) =
  let adds = List.filter_map (function Add c -> Some c | Delete _ -> None) steps in
  Measures.(
    empty
    |> int "size" (List.length adds)
    |> int "literals" (List.fold_left (fun s c -> s + Array.length c) 0 adds)
    |> int "width" (List.fold_left (fun s c -> max s (Array.length c)) 0 adds)
    |> int "deletions" (List.length (List.filter (function Delete _ -> true | Add _ -> false) steps)))

let check (cnf : Cnf.t) (steps : proof) : (Measures.t, string) result =
  if steps = [] then Error "no steps"
  else begin
    let db =
      {
        cl = Vec.create [||];
        alive = Vec.create false;
        dwatch = Hashtbl.create 256;
        units = Hashtbl.create 16;
        empty = 0;
        by_key = Hashtbl.create 256;
        occ = Hashtbl.create 256;
        vals = Array.make (cnf.num_vars + 2) 0;
      }
    in
    Array.iter (fun c -> db_add db (Array.of_list (Clause.lits c))) cnf.clauses;
    let rat_steps = ref 0 in
    let rec go k prefix = function
      | [] -> Error "the empty clause is never added"
      | step :: rest -> (
          let prefix = step :: prefix in
          match step with
          | (Add c | Delete c) when Array.mem 0 c -> Error (Printf.sprintf "step %d: 0 is not a literal" k)
          | Delete c ->
              db_delete db c;
              go (k + 1) prefix rest
          | Add c ->
              let lits = Array.to_list c in
              if (not (rup db lits)) && not (rat db lits && (incr rat_steps; true)) then
                Error (Printf.sprintf "step %d: clause is neither RUP nor RAT" k)
              else begin
                db_add db c;
                if c = [||] then Ok (Measures.int "rat_steps" !rat_steps (measures (List.rev prefix))) else go (k + 1) prefix rest
              end)
    in
    go 0 [] steps
  end

(* ===================================================== the system *)
type config = unit
type input = Cnf.t
type lower_bound = Nothing.t

let name = "drat"
let version = "0.3"

let info =
  {
    group = "logical";
    order = 4;
    line_type = "clause";
    primary_metric = "size";
    book = "";
    simulates = [ "resolution" ];
    description = "DRAT clausal proofs (≡ Extended Resolution); CDCL search, forward checker";
  }

let language = Lang.Cnf
let encoding = None
let params = []
let variants = [ [] ]
let label _ = "DRAT"
let configure _ = Ok ()
let searches () = true

let search () (lim : Limits.t) (cnf : Cnf.t) =
  match solve ~deadline:(Limits.deadline lim) ~max_conflicts:(Limits.size lim 200_000) cnf with
  | s, true ->
      model ~witness:(Assignment.make cnf.num_vars (fun v -> s.assign.(v) = 1)) ~measures:Measures.(empty |> int "conflicts" s.conflicts)
        "CDCL found a satisfying assignment"
  | s, false ->
      let steps = List.map (fun l -> Add (Array.of_list (List.sort (fun a b -> compare (abs a, a) (abs b, b)) l))) (Vec.to_list s.lemmas) in
      refutation ~measures:(Measures.int "conflicts" s.conflicts (measures steps)) steps
  | exception Stop m -> unknown m
  | exception Clock.Timeout -> unknown budget_message

let proof = codec
let lower_bound = Nothing.codec
let verify () cnf p = check cnf p
let check_lower_bound = Nothing.check
let parse_text = Some parse_drat
