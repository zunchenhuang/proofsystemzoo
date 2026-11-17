(* End to end: a fresh database, the starter suite, every default instance
   in parallel, then the report against the expected matrix, caching, the
   audit, and checking proofs from outside. *)
open Proofsystemzoo
open Check

(* Expected cells. Columns whose search is exact or deterministic are
   compared everywhere; the LP/SDP columns only on the instances where they
   finish far inside the budget. *)
let golden =
  {|
benchmark             expect  TT     tree  ord   res   DRAT  NS2  NS3  PC2  PC3  PCR2  PCR3  CP    SOS    DSOS   SA
parity-3              UNSAT   n/a    n/a   n/a   n/a   n/a   n/a  n/a  n/a  n/a  n/a   n/a   4     n/a    n/a    3*
parity-5              UNSAT   n/a    n/a   n/a   n/a   n/a   n/a  n/a  n/a  n/a  n/a   n/a   4     n/a    n/a    4*
php-2-1               UNSAT   4      5     5     5     1     2*   2*   2    2    2     2     4     2      2      1
php-3-2               UNSAT   64     21    20    20    2     4*   4*   3    3    3     3     12    2      4      2*
php-3-3               SAT     sat*   sat*  sat*  sat*  sat*  sat  sat  sat  sat  ≥7    ≥7    sat*  -      -      -
php-4-3               UNSAT   4096   85    68    68    7     6*   6*   4    4    4     4     35    -      -      -
php-5-4               UNSAT   limit  377   247   247   28    ≥6*  ≥6*  5    5    ≥4    ≥4    70    -      -      -
tseitin-cycle-4       UNSAT   16     15    15    15    2     2*   3*   2    2    2     2     17    2      4      2*
tseitin-cycle-6       UNSAT   64     23    23    23    2     2*   3*   2    2    2     2     25    2      4      2*
tseitin-cycle-6-even  SAT     sat*   sat*  sat*  sat*  sat*  sat  sat  sat  sat  sat   sat   sat*  -      -      sat
tseitin-grid-2x3      UNSAT   128    39    35    35    4     3*   4*   3    3    3     3     41    4      4      3*
tseitin-cycle-8       UNSAT   256    31    31    31    2     2*   3*   2    2    2     2     33    2      4      2*
tseitin-grid-3x3      UNSAT   4096   179   103   103   16    4*   6*   4    4    4     4     149   -      -      -
|}

let words s = List.filter (( <> ) "") (String.split_on_char ' ' s)

let () =
  let dir = Filename.concat (Filename.get_temp_dir_name ()) (Printf.sprintf "psz-e2e-%d" (Unix.getpid ())) in
  let path = Filename.concat dir "zoo.db" in
  let st = Store.open_ ~path () in
  List.iter (fun g -> ok "add starter benchmark" (Store.add_generated st g)) (Families.starter ());
  (* the same content under another name is refused; re-adding is idempotent *)
  err "duplicate content refused" (Store.add_generated st ~name:"copy" (Families.php 2));
  ok "re-adding is idempotent" (Store.add_generated st (Families.php 2));
  let benches = Store.list st in
  check "13 benchmarks" (List.length benches = 13);
  (* lazy parsing: the payload parses back to the same content *)
  List.iter (fun (b : Store.benchmark) -> check "payload parses to its hash" (match Lazy.force b.problem with Ok p -> Store.digest p = b.sha | Error _ -> false)) benches;
  let instances = Registry.default_instances () in
  let results = Runner.run_matrix ~timeout:60.0 ~jobs:2 st instances benches in
  check "every job ran" (List.length results = List.length instances * List.length benches);
  List.iter
    (fun (o : Runner.outcome) ->
      check (Printf.sprintf "%s on %s: no problem (%s)" o.system o.benchmark o.message) (not (System.Status.is_problem o.status));
      if o.status = System.Status.Refuted then check "refutations are verified" (o.verified = Some true))
    results;
  (* the report against the expected matrix *)
  let table = Report.matrix st benches in
  let lines = List.filter (fun l -> String.trim l <> "") (String.split_on_char '\n' golden) in
  let header = words (List.hd lines) in
  List.iter
    (fun line ->
      let cells = words line in
      let name = List.hd cells in
      match List.find_opt (fun r -> List.hd r = name) table.rows with
      | None -> fail "report" ("missing row " ^ name)
      | Some row ->
          List.iteri
            (fun i expected ->
              if i >= 2 && expected <> "-" then begin
                let col = List.nth header i in
                let j = let rec find k = function [] -> -1 | h :: t -> if h = col then k else find (k + 1) t in find 0 table.header in
                let got = if j < 0 then "?" else List.nth row j in
                if got <> expected then fail "report" (Printf.sprintf "%s / %s: expected %s, got %s" name col expected got) else incr passed
              end)
            cells)
    (List.tl lines);
  (* a second run reuses every stored run *)
  let again = Runner.run_matrix ~timeout:60.0 ~jobs:2 st instances benches in
  check "second run is fully cached" (List.for_all (fun (o : Runner.outcome) -> o.cached || o.status = System.Status.Not_applicable || o.status = System.Status.Error) again);
  (* every stored proof and certificate re-verifies *)
  let audit = Runner.audit st in
  check "audit covers the stored proofs" (List.length audit > 100);
  List.iter (fun ((r : Store.run), res) -> ok (Printf.sprintf "audit %s on %s" r.system r.benchmark) res) audit;
  (* proofs from outside: DRAT as text, a corrupted JSON proof, a certificate *)
  let b = Option.get (Store.get st "php-4-3") in
  let drat = Result.get_ok (Registry.instance "drat") in
  let stored = List.find (fun (r : Store.run) -> r.proof <> None) (Store.runs ~benchmark:"php-4-3" ~system:"drat" ~with_proof:true st) in
  let text =
    match Drat.codec.decode (Option.get stored.proof) with
    | Ok steps -> String.concat "" (List.map (function Drat.Add c -> String.concat " " (List.map string_of_int (Array.to_list c @ [ 0 ])) ^ "\n" | Drat.Delete c -> "d " ^ String.concat " " (List.map string_of_int (Array.to_list c @ [ 0 ])) ^ "\n") steps)
    | Error e -> failwith e
  in
  check "external DRAT text verifies" ((Runner.check_proof drat b text).status = System.Status.Refuted);
  check "corrupted proof is INVALID" ((Runner.check_proof drat b {|{"format":"drat/1","steps":[["a",[]]]}|}).status = System.Status.Invalid);
  let ns = Result.get_ok (Registry.instance "nullstellensatz[p=2]") in
  let cert = List.find_map (fun (r : Store.run) -> r.certificate) (Store.runs ~benchmark:"php-4-3" ~system:"nullstellensatz[p=2]" ~with_proof:true st) in
  (match cert with
  | Some c -> List.iter (fun (k, r) -> ok ("certificate " ^ k) r) (Runner.check_certificate ns b c)
  | None -> fail "certificate" "no stored NS certificate for php-4-3");
  Store.close st;
  List.iter (fun f -> try Sys.remove (Filename.concat dir f) with Sys_error _ -> ()) (Array.to_list (Sys.readdir dir));
  (try Unix.rmdir dir with Unix.Unix_error _ -> ());
  finish "e2e"
