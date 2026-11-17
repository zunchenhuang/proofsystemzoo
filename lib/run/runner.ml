(* Running systems on benchmarks.

   For each (instance, benchmark) job: convert the benchmark to the
   system's input type, search in a forked child under a hard timeout, send
   the typed outcome back as JSON through a pipe, decode it with the
   system's own codecs, and judge it in the parent:

   - a witness must satisfy the original benchmark (not just the encoding);
   - a lower-bound certificate must pass the system's checker;
   - a refutation must pass the system's verifier, and is UNSOUND if the
     benchmark is known to be satisfiable (likewise a SAT claim on an
     unsatisfiable one).

   Up to [jobs] children run at once; results are delivered as they finish. *)
open System

type outcome = {
  benchmark : string;
  system : string;
  version : string;
  status : Status.t;
  verified : bool option;
  measures : Measures.t;
  message : string;
  search_time : float;
  verify_time : float option;
  encoding : string option;
  proof : Json.t option; (* verified refutations only *)
  certificate : Json.t option; (* accepted witness / lower bound *)
  cached : bool;
}

let blank ~(b : Store.benchmark) ~id ~version =
  {
    benchmark = b.name;
    system = id;
    version;
    status = Status.Not_applicable;
    verified = None;
    measures = Measures.empty;
    message = "";
    search_time = 0.0;
    verify_time = None;
    encoding = None;
    proof = None;
    certificate = None;
    cached = false;
  }

(* ------------------------------------------------------------ judging *)

(* Everything here is typed by the instance: the outcome arrives as JSON
   and is decoded with the system's codecs before anything is checked. *)
let judge (type c i p l) (module S : System.S with type config = c and type input = i and type proof = p and type lower_bound = l) ~(config : c) ~id
    ~(b : Store.benchmark) ~(original : Lang.problem) ~(input : i) ~encoding ~search_time (o : (p, l) System.outcome) : outcome =
  let base = { (blank ~b ~id ~version:S.version) with encoding; search_time } in
  let invalid ?(measures = Measures.empty) msg = { base with status = Status.Invalid; measures; message = msg } in
  let lower_bound measures = function
    | None -> Ok (measures, [])
    | Some lb -> (
        match S.check_lower_bound config input lb with
        | Ok m -> Ok (Measures.union measures m, [ ("lower_bound", S.lower_bound.encode lb) ])
        | Error e -> Error ("lower-bound certificate rejected: " ^ e))
  in
  let cert fields = if fields = [] then None else Some (`Assoc fields) in
  match o with
  | Model m -> (
      match m.witness with
      | Some w when not (Lang.problem_eval original w) -> invalid ~measures:m.measures "witness does not satisfy the benchmark"
      | witness ->
          let measures = if witness = None then m.measures else Measures.flag "witness" true m.measures in
          let certificate = Option.map (fun w -> `Assoc [ ("witness", Assignment.codec.encode w) ]) witness in
          if b.expected = Some Families.Unsat then { base with status = Status.Unsound; measures; message = "claimed SAT on an unsatisfiable benchmark" }
          else { base with status = Status.Satisfiable; measures; message = m.message; certificate })
  | Unknown u -> (
      match lower_bound u.measures u.lower_bound with
      | Error e -> invalid ~measures:u.measures e
      | Ok (measures, fields) -> { base with status = Status.Limit; measures; message = u.message; certificate = cert fields })
  | Refutation r -> (
      match lower_bound r.measures r.lower_bound with
      | Error e -> invalid ~measures:r.measures e
      | Ok (measures, fields) -> (
          let v, vt = Clock.time (fun () -> S.verify config input r.proof) in
          match v with
          | Error e -> { base with status = Status.Invalid; verified = Some false; measures; message = "verification failed: " ^ e; verify_time = Some vt }
          | Ok vm ->
              let measures = Measures.union measures vm in
              let proof = Some (S.proof.encode r.proof) in
              if b.expected = Some Families.Sat then
                { base with status = Status.Unsound; verified = Some true; measures; message = "verified refutation of a satisfiable benchmark"; verify_time = Some vt; proof }
              else { base with status = Status.Refuted; verified = Some true; measures; verify_time = Some vt; proof; certificate = cert fields }))

(* ------------------------------------------------------------ children *)

type pending = {
  pid : int;
  fd : Unix.file_descr;
  buf : Buffer.t;
  deadline : float;
  t0 : float;
  finish : [ `Data of string | `Timeout | `Died of string ] -> float -> outcome;
}

type started = Done of outcome | Pending of pending

let write_all fd s =
  let b = Bytes.unsafe_of_string s in
  let rec go off = if off < Bytes.length b then go (off + Unix.write fd b off (Bytes.length b - off)) in
  go 0

let start ?(timeout = 30.0) ?(limits = Limits.none) (inst : instance) (b : Store.benchmark) : started =
  let (module I : INSTANCE) = inst in
  let module S = I.S in
  let base = blank ~b ~id:I.id ~version:S.version in
  match Lazy.force b.problem with
  | Error e -> Done { base with status = Status.Error; message = "cannot parse the benchmark: " ^ e }
  | Ok original -> (
      match Encodings.convert ?prefer:S.encoding S.language original with
      | Error e -> Done { base with message = e }
      | Ok (input, encoding) ->
          if not (S.searches I.config) then Done { base with encoding; message = "verifier-only system" }
          else begin
            let limits = if limits.time = None then Limits.with_time (Some (0.9 *. timeout)) limits else limits in
            let ocodec = System.outcome_codec S.proof S.lower_bound in
            flush_all ();
            let rd, wr = Unix.pipe () in
            let t0 = Clock.now () in
            match Unix.fork () with
            | 0 ->
                Unix.close rd;
                let msg =
                  match S.search I.config limits input with
                  | o -> `Assoc [ ("ok", ocodec.encode o) ]
                  | exception Clock.Timeout -> `Assoc [ ("ok", ocodec.encode (unknown budget_message)) ]
                  | exception e -> `Assoc [ ("crash", `String (Printexc.to_string e)) ]
                in
                (try write_all wr (Json.to_string msg) with _ -> ());
                Unix._exit 0
            | pid ->
                Unix.close wr;
                let finish result elapsed =
                  let fail status msg = { base with encoding; status; message = msg; search_time = elapsed } in
                  match result with
                  | `Timeout -> fail Status.Timeout (Printf.sprintf "killed after %.1fs" timeout)
                  | `Died why -> fail Status.Error why
                  | `Data s -> (
                      let open Json in
                      match of_string s with
                      | Error e -> fail Status.Error ("child sent malformed data: " ^ e)
                      | Ok j -> (
                          match (D.field_opt "ok" (fun x -> Ok x) j, D.field_opt "crash" D.string j) with
                          | Ok (Some o), _ -> (
                              match ocodec.decode o with
                              | Ok o -> judge (module S) ~config:I.config ~id:I.id ~b ~original ~input ~encoding ~search_time:elapsed o
                              | Error e -> fail Status.Error ("undecodable outcome: " ^ e))
                          | _, Ok (Some e) -> fail Status.Error e
                          | _ -> fail Status.Error "child sent no outcome"))
                in
                Pending { pid; fd = rd; buf = Buffer.create 4096; deadline = t0 +. timeout; t0; finish }
          end)

let reap p =
  let _, st = Unix.waitpid [] p.pid in
  match st with Unix.WEXITED c -> Printf.sprintf "child exited (%d)" c | Unix.WSIGNALED s -> Printf.sprintf "child killed by signal %d" s | Unix.WSTOPPED _ -> "child stopped"

(* run [tasks] with at most [jobs] children at a time; [on_done] gets every
   outcome as soon as it is known *)
let run_all ?(jobs = 1) (tasks : (unit -> started) list) (on_done : outcome -> unit) =
  let queue = Queue.of_seq (List.to_seq tasks) and running = ref [] in
  let chunk = Bytes.create 65536 in
  let complete p result =
    Unix.close p.fd;
    let why = reap p in
    let result = match result with `Data "" -> `Died why | r -> r in
    running := List.filter (fun q -> q.pid <> p.pid) !running;
    on_done (p.finish result (Clock.now () -. p.t0))
  in
  let rec loop () =
    while List.length !running < max 1 jobs && not (Queue.is_empty queue) do
      match (Queue.pop queue) () with Done o -> on_done o | Pending p -> running := p :: !running
    done;
    if !running <> [] then begin
      let now = Clock.now () in
      let wait = List.fold_left (fun m p -> Float.min m (p.deadline -. now)) 1.0 !running in
      let ready = match Unix.select (List.map (fun p -> p.fd) !running) [] [] (Float.max 0.0 wait) with r, _, _ -> r | exception Unix.Unix_error (Unix.EINTR, _, _) -> [] in
      List.iter
        (fun p ->
          if List.mem p.fd ready then
            match Unix.read p.fd chunk 0 (Bytes.length chunk) with
            | 0 -> complete p (`Data (Buffer.contents p.buf))
            | n -> Buffer.add_subbytes p.buf chunk 0 n
            | exception Unix.Unix_error (Unix.EINTR, _, _) -> ())
        !running;
      let now = Clock.now () in
      List.iter
        (fun p ->
          if now > p.deadline then begin
            (try Unix.kill p.pid Sys.sigkill with Unix.Unix_error _ -> ());
            complete p `Timeout
          end)
        !running;
      loop ()
    end
  in
  loop ()

(* ------------------------------------------------------------ the matrix *)

let config_json (inst : instance) timeout (limits : Limits.t) : Json.t =
  let (module I : INSTANCE) = inst in
  let fields = List.map (fun (k, v) -> (k, `String v)) I.env @ [ ("timeout", `Float timeout) ] @ Limits.to_fields limits in
  `Assoc (List.sort (fun (a, _) (b, _) -> compare a b) fields)

let of_run (r : Store.run) =
  {
    benchmark = r.benchmark;
    system = r.system;
    version = r.system_version;
    status = r.status;
    verified = r.verified;
    measures = r.measures;
    message = Option.value r.message ~default:"";
    search_time = Option.value r.search_time ~default:0.0;
    verify_time = r.verify_time;
    encoding = r.encoding;
    proof = None;
    certificate = None;
    cached = true;
  }

let record st (b : Store.benchmark) ~config ~keep_proofs (o : outcome) =
  if o.status <> Status.Not_applicable then
    ignore
      (Store.record_run st b ~system:o.system ~version:o.version ~status:o.status ?encoding:o.encoding ~config ?verified:o.verified ~measures:o.measures
         ~message:o.message
         ?proof:(if keep_proofs && o.status = Status.Refuted then o.proof else None)
         ~search_time:o.search_time ?verify_time:o.verify_time
         ?certificate:(if keep_proofs then o.certificate else None)
         ())

(* every instance on every benchmark; runs with the same system version and
   configuration are reused unless [force] *)
let run_matrix ?(timeout = 30.0) ?(limits = Limits.none) ?(jobs = 1) ?(keep_proofs = true) ?(force = false) ?(progress = fun _ -> ()) (st : Store.t)
    (instances : instance list) (benches : Store.benchmark list) : outcome list =
  let results = ref [] in
  let tasks =
    List.concat_map
      (fun inst ->
        let (module I : INSTANCE) = inst in
        let config = config_json inst timeout limits in
        let cached = Hashtbl.create 32 in
        if not force then
          List.iter
            (fun (r : Store.run) -> if r.system_version = I.S.version && r.config = config then Hashtbl.replace cached r.benchmark r)
            (Store.runs ~system:I.id st);
        List.map
          (fun (b : Store.benchmark) () ->
            match Hashtbl.find_opt cached b.name with
            | Some r -> Done (of_run r)
            | None -> (
                match start ~timeout ~limits inst b with
                | Done o -> Done o
                | Pending p ->
                    Pending { p with finish = (fun r t -> let o = p.finish r t in record st b ~config ~keep_proofs o; o) }))
          benches)
      instances
  in
  (* record cached-free immediate results too (errors, n/a are not stored) *)
  let by_name = Hashtbl.create 64 in
  List.iter (fun (b : Store.benchmark) -> Hashtbl.replace by_name b.name b) benches;
  run_all ~jobs tasks (fun o ->
      if (not o.cached) && o.status = Status.Error && o.search_time = 0.0 then
        Option.iter (fun b -> record st b ~config:(`Assoc []) ~keep_proofs o) (Hashtbl.find_opt by_name o.benchmark);
      results := o :: !results;
      progress o);
  List.rev !results

(* ------------------------------------------------------------ external proofs *)

(* verify a proof given as JSON (or the system's native text) *)
let check_proof (inst : instance) (b : Store.benchmark) (text : string) : outcome =
  let (module I : INSTANCE) = inst in
  let module S = I.S in
  let base = blank ~b ~id:I.id ~version:S.version in
  let fail msg = { base with status = Status.Invalid; verified = Some false; message = msg } in
  match Lazy.force b.problem with
  | Error e -> { base with status = Status.Error; message = e }
  | Ok original -> (
      match Encodings.convert ?prefer:S.encoding S.language original with
      | Error e -> { base with message = e }
      | Ok (input, encoding) -> (
          (* JSON first; a system with a native text format gets a second try *)
          let decoded =
            let json = match Json.of_string text with Ok j -> S.proof.decode j | Error e -> Error e in
            match (json, S.parse_text) with
            | Ok p, _ -> Ok p
            | Error e, Some parse -> ( match parse text with Ok p -> Ok p | Error e' -> Error (e ^ "; as text: " ^ e'))
            | Error e, None -> Error e
          in
          match decoded with
          | Error e -> { (fail ("cannot read the proof: " ^ e)) with encoding }
          | Ok proof -> judge (module S) ~config:I.config ~id:I.id ~b ~original ~input ~encoding ~search_time:0.0 (refutation proof)))

(* check a certificate object {"witness": …} and/or {"lower_bound": …} *)
let check_certificate (inst : instance) (b : Store.benchmark) (cert : Json.t) : (string * (string, string) result) list =
  let (module I : INSTANCE) = inst in
  let module S = I.S in
  match Lazy.force b.problem with
  | Error e -> [ ("benchmark", Error e) ]
  | Ok original ->
      let field k = match cert with `Assoc l -> List.assoc_opt k l | _ -> None in
      let witness =
        match field "witness" with
        | None -> []
        | Some w -> (
            match Assignment.codec.decode w with
            | Ok a -> [ ("witness", if Lang.problem_eval original a then Ok "satisfies the benchmark" else Error "does not satisfy the benchmark") ]
            | Error e -> [ ("witness", Error e) ])
      in
      let lb =
        match field "lower_bound" with
        | None -> []
        | Some l -> (
            match (S.lower_bound.decode l, Encodings.convert ?prefer:S.encoding S.language original) with
            | Error e, _ | _, Error e -> [ ("lower_bound", Error e) ]
            | Ok lb, Ok (input, _) -> (
                match S.check_lower_bound I.config input lb with
                | Ok m -> [ ("lower_bound", Ok ("certified: " ^ Json.to_string (Measures.to_json m))) ]
                | Error e -> [ ("lower_bound", Error e) ]))
      in
      witness @ lb

(* ------------------------------------------------------------ audit *)

(* re-verify every stored proof and certificate with the current verifiers *)
let audit (st : Store.t) : (Store.run * (string, string) result) list =
  let benches = Hashtbl.create 64 in
  List.iter (fun (b : Store.benchmark) -> Hashtbl.replace benches b.name b) (Store.list st);
  List.filter_map
    (fun (r : Store.run) ->
      match (r.proof, r.certificate) with
      | None, None -> None
      | proof, certificate -> (
          match (Registry.instance r.system, Hashtbl.find_opt benches r.benchmark) with
          | Error e, _ -> Some (r, Error e)
          | _, None -> Some (r, Error "benchmark missing")
          | Ok inst, Some b ->
              let p =
                match proof with
                | None -> Ok "no proof"
                | Some j ->
                    let o = check_proof inst b (Json.to_string j) in
                    if o.status = Status.Refuted then Ok (Measures.summary ~keys:[ "size"; "degree"; "width" ] o.measures) else Error o.message
              in
              let c =
                match certificate with
                | None -> []
                | Some c -> check_certificate inst b c
              in
              let bad = List.filter_map (fun (k, v) -> match v with Error e -> Some (k ^ ": " ^ e) | Ok _ -> None) c in
              Some
                ( r,
                  match (p, bad) with
                  | Error e, _ -> Error e
                  | Ok s, [] -> Ok (s ^ if c = [] then "" else " + " ^ String.concat ", " (List.map fst c))
                  | Ok _, bad -> Error (String.concat "; " bad) )))
    (Store.runs ~with_proof:true st)
