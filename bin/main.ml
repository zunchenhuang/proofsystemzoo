(* proofsystemzoo: command-line interface *)
open Proofsystemzoo

let usage =
  {|proofsystemzoo - a zoo of propositional proof systems over one local benchmark database

usage: proofsystemzoo [--db PATH] COMMAND [ARGS]

benchmarks
  init [--no-seed]                  create the database (seeded with the starter suite)
  list [--family F] [--language L] [--max-vars N] [--tag T]
  show NAME [--payload]             details, runs and (optionally) the instance text
  add FILE [--name N] [--language cnf|poly|ineq] [--expected SAT|UNSAT] [--family F] [--tags a,b]
  gen FAMILY [KEY=VALUE ...] [--name N]
                                    add a generated instance (see: families)
  remove NAME
  families                          benchmark generators and their parameters
  encodings                         translations between input languages

systems
  systems                           systems, parameters, inputs and measures
  zoo                               the map of the zoo, by group
  run [--systems ID,...] [--benchmarks NAME,...] [--family F] [--timeout S] [--jobs N]
      [--limit KEY=VALUE]... [--force] [--no-proofs]
                                    run systems on benchmarks (cached by version + config)
  report [--format text|md|csv] [--systems ID,...] [--family F]

proofs and certificates
  proof NAME SYSTEM                 print the stored proof (JSON)
  certificate NAME SYSTEM           print the stored certificates (witness, lower bound)
  check NAME SYSTEM FILE            verify a proof file (JSON, or native text such as DRAT)
  check-cert NAME SYSTEM FILE       check {"witness": ...} and/or {"lower_bound": ...}
  audit                             re-verify every stored proof and certificate

A SYSTEM is a name with optional parameters, e.g. nullstellensatz[p=3] or
sum-of-squares[cone=dsos]. Limits: time, max_degree, max_width, max_vars, max_size.
The database is $PROOFSYSTEMZOO_DB, or ~/.proofsystemzoo/zoo.db.
|}

exception Usage of string

let fail fmt = Printf.ksprintf (fun s -> raise (Usage s)) fmt

(* ------------------------------------------------------------ arguments *)
type args = { pos : string list; opts : (string * string) list; flags : string list }

let parse_args ~flags argv =
  let rec go acc = function
    | [] -> { acc with pos = List.rev acc.pos; opts = List.rev acc.opts }
    | a :: rest when String.length a > 2 && String.sub a 0 2 = "--" -> (
        let k = String.sub a 2 (String.length a - 2) in
        match String.index_opt k '=' with
        | Some i -> go { acc with opts = (String.sub k 0 i, String.sub k (i + 1) (String.length k - i - 1)) :: acc.opts } rest
        | None when List.mem k flags -> go { acc with flags = k :: acc.flags } rest
        | None -> ( match rest with v :: rest -> go { acc with opts = (k, v) :: acc.opts } rest | [] -> fail "--%s needs a value" k))
    | a :: rest -> go { acc with pos = a :: acc.pos } rest
  in
  go { pos = []; opts = []; flags = [] } argv

let opt a k = List.assoc_opt k a.opts
let opts a k = List.filter_map (fun (k', v) -> if k = k' then Some v else None) a.opts
let flag a k = List.mem k a.flags
let commas s = List.filter (( <> ) "") (List.map String.trim (String.split_on_char ',' s))

let int_opt a k =
  Option.map (fun v -> match int_of_string_opt v with Some i -> i | None -> fail "--%s: not an integer: %s" k v) (opt a k)

let float_opt a k =
  Option.map (fun v -> match float_of_string_opt v with Some f -> f | None -> fail "--%s: not a number: %s" k v) (opt a k)

let ok = function Ok x -> x | Error e -> raise (Usage e)
let read_file path = In_channel.with_open_bin path In_channel.input_all

(* ------------------------------------------------------------ printing *)
let table header rows =
  let t = { Report.header; rows; legend = [] } in
  let s = Report.render_text t in
  (* drop the legend footer *)
  match String.index_opt s '\n' with
  | None -> print_string s
  | Some _ ->
      let lines = String.split_on_char '\n' s in
      let n = List.length rows + 2 in
      List.iteri (fun i l -> if i < n then print_endline l) lines

let bench_or_fail st name = match Store.get st name with Some b -> b | None -> fail "no benchmark named %s" name

let instance_or_fail id = ok (Registry.instance id)

(* ------------------------------------------------------------ commands *)
let cmd_init st a =
  if not (flag a "no-seed") then
    List.iter
      (fun g ->
        match Store.add_generated st g with
        | Ok b -> Printf.printf "  %-24s %s\n" b.Store.name b.sha
        | Error e -> Printf.printf "  %-24s skipped: %s\n" g.Families.name e)
      (Families.starter ());
  Printf.printf "database: %s (%d benchmarks)\n" st.Store.path (List.length (Store.list st))

let cmd_list st a =
  let filter = { Store.all with family = opt a "family"; language = opt a "language"; max_vars = int_opt a "max-vars"; tag = opt a "tag" } in
  let bs = Store.list ~filter st in
  table
    [ "name"; "family"; "lang"; "vars"; "cons"; "width"; "expect"; "tags" ]
    (List.map
       (fun (b : Store.benchmark) ->
         [
           b.name;
           b.family;
           b.language;
           string_of_int b.num_vars;
           string_of_int b.num_constraints;
           string_of_int b.max_width;
           (match b.expected with Some e -> Families.expected_to_string e | None -> "?");
           String.concat "," b.tags;
         ])
       bs)

let cmd_show st a =
  let name = match a.pos with [ n ] -> n | _ -> fail "usage: show NAME [--payload]" in
  let b = bench_or_fail st name in
  Printf.printf "name      %s\nfamily    %s %s\nlanguage  %s\nexpected  %s\nsize      %d variables, %d constraints, max width/degree %d\nsha256    %s\ntags      %s\n" b.name
    b.family (Json.to_string b.params) b.language
    (match b.expected with Some e -> Families.expected_to_string e | None -> "unknown")
    b.num_vars b.num_constraints b.max_width b.sha (String.concat ", " b.tags);
  let runs = Store.runs ~benchmark:name ~latest_only:true st in
  if runs <> [] then begin
    print_endline "\nruns (latest per system)";
    table
      [ "system"; "status"; "measures"; "time"; "message" ]
      (List.map
         (fun (r : Store.run) ->
           [
             r.system;
             System.Status.to_string r.status;
             Measures.summary r.measures;
             (match r.search_time with Some t -> Printf.sprintf "%.2fs" t | None -> "");
             Option.value r.message ~default:"";
           ])
         runs)
  end;
  if flag a "payload" then print_string ("\n" ^ b.payload)

let language_of_file path =
  match String.lowercase_ascii (Filename.extension path) with
  | ".cnf" | ".dimacs" -> "cnf"
  | ".poly" -> "poly"
  | ".opb" | ".ineq" | ".pb" -> "ineq"
  | e -> fail "cannot tell the language of %s from %S: use --language cnf|poly|ineq" path e

let cmd_add st a =
  let path = match a.pos with [ p ] -> p | _ -> fail "usage: add FILE [--name N] [--language L] [--expected SAT|UNSAT]" in
  let lang = match opt a "language" with Some l -> l | None -> language_of_file path in
  let p = ok (Lang.parse lang (read_file path)) in
  let expected =
    Option.map (fun e -> match Families.expected_of_string (String.uppercase_ascii e) with Some e -> e | None -> fail "--expected must be SAT or UNSAT") (opt a "expected")
  in
  let name = Option.value (opt a "name") ~default:(Filename.remove_extension (Filename.basename path)) in
  let b =
    ok (Store.add st ?family:(opt a "family") ?expected ~tags:(Option.fold ~none:[] ~some:commas (opt a "tags")) p name)
  in
  Printf.printf "%s  %s  (%d variables, %d constraints)\n" b.name b.sha b.num_vars b.num_constraints

(* KEY=VALUE with JSON values; "2x3" is the pair [2, 3] *)
let param_value v =
  match String.split_on_char 'x' v with
  | [ r; c ] when int_of_string_opt r <> None && int_of_string_opt c <> None -> `List [ `Int (int_of_string r); `Int (int_of_string c) ]
  | _ -> ( match Json.of_string v with Ok j -> j | Error _ -> `String v)

let cmd_gen st a =
  match a.pos with
  | family :: kvs ->
      let params =
        List.map (fun kv -> match String.index_opt kv '=' with Some i -> (String.sub kv 0 i, param_value (String.sub kv (i + 1) (String.length kv - i - 1))) | None -> fail "expected KEY=VALUE, got %s" kv) kvs
      in
      let g = ok (Families.generate family params) in
      let b = ok (Store.add_generated st ?name:(opt a "name") g) in
      Printf.printf "%s  %s  (%d variables, %d constraints, expected %s)\n" b.name b.sha b.num_vars b.num_constraints
        (match b.expected with Some e -> Families.expected_to_string e | None -> "?")
  | [] -> fail "usage: gen FAMILY [KEY=VALUE ...]"

let cmd_families () = List.iter (fun (f : Families.family) -> Printf.printf "  %-10s %s\n" f.fname f.doc) Families.families

let cmd_encodings () =
  List.iter
    (fun e ->
      let name, src, dst, doc = Encodings.describe e in
      Printf.printf "  %-14s %s -> %s   %s\n" name src dst doc)
    Encodings.all

let cmd_systems () =
  table
    [ "system"; "version"; "group"; "reads"; "measure"; "parameters"; "variants" ]
    (List.map
       (fun (module S : System.S) ->
         [
           S.name;
           S.version;
           S.info.group;
           (Lang.name S.language ^ match S.encoding with Some e -> " <- " ^ e | None -> "");
           S.info.primary_metric;
           String.concat ", " (List.map (fun (p : Param.spec) -> p.key ^ "=" ^ p.default) S.params);
           String.concat " " (List.map (fun v -> Param.id S.name v) S.variants);
         ])
       (Registry.systems ()))

let summary_line (o : Runner.outcome) =
  Printf.sprintf "%-24s %-30s %-11s %-34s %6.2fs%s%s" o.benchmark o.system (System.Status.to_string o.status) (Measures.summary o.measures) o.search_time
    (if o.cached then " (cached)" else "")
    (if o.message <> "" && o.status <> System.Status.Refuted then "  " ^ o.message else "")

let cmd_run st a =
  let instances = match opt a "systems" with Some s -> List.map instance_or_fail (commas s) | None -> Registry.default_instances () in
  let filter = { Store.all with family = opt a "family"; names = Option.fold ~none:[] ~some:commas (opt a "benchmarks") } in
  let benches = Store.list ~filter st in
  if benches = [] then fail "no benchmarks selected (run init first?)";
  let limits =
    ok (Limits.of_pairs (List.map (fun kv -> match String.index_opt kv '=' with Some i -> (String.sub kv 0 i, String.sub kv (i + 1) (String.length kv - i - 1)) | None -> fail "--limit expects KEY=VALUE") (opts a "limit")))
  in
  let timeout = Option.value (float_opt a "timeout") ~default:30.0 and jobs = Option.value (int_opt a "jobs") ~default:1 in
  let total = List.length instances * List.length benches and k = ref 0 in
  let t0 = Clock.now () in
  let results =
    Runner.run_matrix ~timeout ~limits ~jobs ~keep_proofs:(not (flag a "no-proofs")) ~force:(flag a "force")
      ~progress:(fun o ->
        incr k;
        if o.status <> System.Status.Not_applicable then Printf.printf "[%d/%d] %s\n%!" !k total (summary_line o))
      st instances benches
  in
  let count s = List.length (List.filter (fun (o : Runner.outcome) -> o.status = s) results) in
  let problems = List.filter (fun (o : Runner.outcome) -> System.Status.is_problem o.status) results in
  Printf.printf "\n%d jobs in %.1fs (%d parallel): %d refuted, %d satisfiable, %d limit, %d timeout, %d n/a, %d problems\n" total (Clock.now () -. t0) jobs
    (count System.Status.Refuted) (count System.Status.Satisfiable) (count System.Status.Limit) (count System.Status.Timeout)
    (count System.Status.Not_applicable) (List.length problems);
  List.iter (fun o -> Printf.printf "  PROBLEM %s\n" (summary_line o)) problems;
  if problems <> [] then exit 1

let cmd_report st a =
  let filter = { Store.all with family = opt a "family" } in
  let t = Report.matrix ?only:(Option.map commas (opt a "systems")) st (Store.list ~filter st) in
  print_string
    (match opt a "format" with
    | None | Some "text" -> Report.render_text t
    | Some "md" -> Report.render_md t
    | Some "csv" -> Report.render_csv t
    | Some f -> fail "unknown format %s (text, md, csv)" f)

let latest_run st name id pred =
  List.find_opt pred (List.rev (Store.runs ~benchmark:name ~system:id ~with_proof:true st))

let cmd_proof st a =
  match a.pos with
  | [ name; id ] -> (
      let id = System.instance_id (instance_or_fail id) in
      match latest_run st name id (fun r -> r.proof <> None) with
      | Some { proof = Some p; _ } -> print_endline (Yojson.Safe.pretty_to_string p)
      | _ -> fail "no stored proof for %s on %s" id name)
  | _ -> fail "usage: proof NAME SYSTEM"

let cmd_certificate st a =
  match a.pos with
  | [ name; id ] -> (
      let id = System.instance_id (instance_or_fail id) in
      match latest_run st name id (fun r -> r.certificate <> None) with
      | Some { certificate = Some c; _ } -> print_endline (Yojson.Safe.pretty_to_string c)
      | _ -> fail "no stored certificate for %s on %s" id name)
  | _ -> fail "usage: certificate NAME SYSTEM"

let cmd_check st a =
  match a.pos with
  | [ name; id; file ] ->
      let o = Runner.check_proof (instance_or_fail id) (bench_or_fail st name) (read_file file) in
      Printf.printf "%s %s\n" (System.Status.to_string o.status) (if o.status = System.Status.Refuted then Json.to_string (Measures.to_json o.measures) else o.message);
      if o.status <> System.Status.Refuted then exit 1
  | _ -> fail "usage: check NAME SYSTEM FILE"

let cmd_check_cert st a =
  match a.pos with
  | [ name; id; file ] ->
      let cert = ok (Json.of_string (read_file file)) in
      let results = Runner.check_certificate (instance_or_fail id) (bench_or_fail st name) cert in
      if results = [] then fail "the file has neither a \"witness\" nor a \"lower_bound\"";
      List.iter (fun (k, r) -> match r with Ok s -> Printf.printf "%-12s OK  %s\n" k s | Error e -> Printf.printf "%-12s BAD %s\n" k e) results;
      if List.exists (fun (_, r) -> Result.is_error r) results then exit 1
  | _ -> fail "usage: check-cert NAME SYSTEM FILE"

let cmd_audit st =
  let results = Runner.audit st in
  let bad = List.filter (fun (_, r) -> Result.is_error r) results in
  List.iter
    (fun ((r : Store.run), res) ->
      match res with
      | Ok s -> Printf.printf "OK   %-24s %-30s %s\n" r.benchmark r.system s
      | Error e -> Printf.printf "FAIL %-24s %-30s %s\n" r.benchmark r.system e)
    results;
  Printf.printf "\n%d stored proofs/certificates re-checked, %d failed\n" (List.length results) (List.length bad);
  if bad <> [] then exit 1

let main argv =
  let a = parse_args ~flags:[ "no-seed"; "payload"; "force"; "no-proofs"; "help" ] argv in
  match a.pos with
  | [] | "help" :: _ -> print_string usage
  | _ when flag a "help" -> print_string usage
  | cmd :: rest -> (
      let a = { a with pos = rest } in
      let with_store f =
        let st = Store.open_ ?path:(opt a "db") () in
        Fun.protect ~finally:(fun () -> Store.close st) (fun () -> f st)
      in
      match cmd with
      | "init" -> with_store (fun st -> cmd_init st a)
      | "list" -> with_store (fun st -> cmd_list st a)
      | "show" -> with_store (fun st -> cmd_show st a)
      | "add" -> with_store (fun st -> cmd_add st a)
      | "gen" -> with_store (fun st -> cmd_gen st a)
      | "remove" -> with_store (fun st -> match a.pos with [ n ] -> ignore (bench_or_fail st n); Store.remove st n | _ -> fail "usage: remove NAME")
      | "families" -> cmd_families ()
      | "encodings" -> cmd_encodings ()
      | "systems" -> cmd_systems ()
      | "zoo" -> print_string (Report.zoo ())
      | "run" -> with_store (fun st -> cmd_run st a)
      | "report" -> with_store (fun st -> cmd_report st a)
      | "proof" -> with_store (fun st -> cmd_proof st a)
      | "certificate" -> with_store (fun st -> cmd_certificate st a)
      | "check" -> with_store (fun st -> cmd_check st a)
      | "check-cert" -> with_store (fun st -> cmd_check_cert st a)
      | "audit" -> with_store cmd_audit
      | c -> fail "unknown command %s (try: proofsystemzoo help)" c)

let () =
  try main (List.tl (Array.to_list Sys.argv)) with
  | Usage msg ->
      prerr_endline ("error: " ^ msg);
      exit 2
  | Store.Db_error msg ->
      prerr_endline ("database error: " ^ msg);
      exit 2
  | Sys_error msg ->
      prerr_endline ("error: " ^ msg);
      exit 2
