(* The local benchmark database (SQLite, schema version 2).

   Benchmarks are stored as canonical text with a content hash
   "language:sha256", so a family instance generated twice, or added from a
   file, is recognised as the same benchmark. Runs record what a system did
   on a benchmark: status, measures, timings, the verified proof and the
   accepted certificates, all as JSON in the formats of the systems. Parsing
   a payload is lazy: listing a thousand benchmarks parses none of them. *)

let schema_version = 2

let schema =
  {|
CREATE TABLE IF NOT EXISTS meta (
    key   TEXT PRIMARY KEY,
    value TEXT NOT NULL
);
CREATE TABLE IF NOT EXISTS benchmarks (
    id          INTEGER PRIMARY KEY,
    name        TEXT NOT NULL UNIQUE,
    family      TEXT NOT NULL,
    language    TEXT NOT NULL,
    params      TEXT NOT NULL DEFAULT '{}',
    expected    TEXT CHECK (expected IN ('SAT','UNSAT') OR expected IS NULL),
    num_vars    INTEGER NOT NULL,
    num_constraints INTEGER NOT NULL,
    max_width   INTEGER NOT NULL,
    sha256      TEXT NOT NULL UNIQUE,
    payload     TEXT NOT NULL,
    tags        TEXT NOT NULL DEFAULT '[]',
    created_at  REAL NOT NULL
);
CREATE INDEX IF NOT EXISTS idx_bench_family ON benchmarks(family);
CREATE TABLE IF NOT EXISTS runs (
    id             INTEGER PRIMARY KEY,
    benchmark_id   INTEGER NOT NULL REFERENCES benchmarks(id) ON DELETE CASCADE,
    system         TEXT NOT NULL,
    system_version TEXT NOT NULL,
    encoding       TEXT,
    config         TEXT NOT NULL DEFAULT '{}',
    status         TEXT NOT NULL,
    verified       INTEGER,
    metrics        TEXT NOT NULL DEFAULT '{}',
    message        TEXT,
    proof          TEXT,
    search_time    REAL,
    verify_time    REAL,
    created_at     REAL NOT NULL,
    certificate    TEXT
);
CREATE INDEX IF NOT EXISTS idx_runs_bench  ON runs(benchmark_id);
CREATE INDEX IF NOT EXISTS idx_runs_system ON runs(system);
|}

type benchmark = {
  id : int;
  name : string;
  family : string;
  language : string;
  params : Json.t;
  expected : Families.expected option;
  num_vars : int;
  num_constraints : int;
  max_width : int;
  sha : string;
  tags : string list;
  payload : string;
  problem : (Lang.problem, string) result Lazy.t;
}

type run = {
  rid : int;
  benchmark : string;
  system : string;
  system_version : string;
  encoding : string option;
  config : Json.t;
  status : System.Status.t;
  verified : bool option;
  measures : Measures.t;
  message : string option;
  proof : Json.t option;
  search_time : float option;
  verify_time : float option;
  certificate : Json.t option;
}

type t = { db : Sqlite3.db; path : string }

exception Db_error of string

let default_path () =
  match Sys.getenv_opt "PROOFSYSTEMZOO_DB" with
  | Some p when p <> "" -> p
  | _ -> Filename.concat (Filename.concat (try Sys.getenv "HOME" with Not_found -> ".") ".proofsystemzoo") "zoo.db"

let check db what = function
  | Sqlite3.Rc.OK | Sqlite3.Rc.DONE | Sqlite3.Rc.ROW -> ()
  | rc -> raise (Db_error (Printf.sprintf "sqlite %s: %s (%s)" what (Sqlite3.Rc.to_string rc) (Sqlite3.errmsg db)))

let exec t sql = check t.db sql (Sqlite3.exec t.db sql)

let rec mkdir_p d =
  if d <> "" && d <> "/" && d <> "." && not (Sys.file_exists d) then begin
    mkdir_p (Filename.dirname d);
    try Unix.mkdir d 0o755 with Unix.Unix_error (Unix.EEXIST, _, _) -> ()
  end

(* rows as functions from column name to value *)
let query t sql (args : Sqlite3.Data.t list) (f : (string -> Sqlite3.Data.t) -> 'a) : 'a list =
  let st = Sqlite3.prepare t.db sql in
  List.iteri (fun i a -> check t.db "bind" (Sqlite3.bind st (i + 1) a)) args;
  let names = lazy (Array.init (Sqlite3.column_count st) (Sqlite3.column_name st)) in
  let rec loop acc =
    match Sqlite3.step st with
    | Sqlite3.Rc.ROW ->
        let row = Sqlite3.row_data st and names = Lazy.force names in
        let get k =
          let rec find i = if i >= Array.length names then raise (Db_error ("no column " ^ k)) else if names.(i) = k then row.(i) else find (i + 1) in
          find 0
        in
        loop (f get :: acc)
    | Sqlite3.Rc.DONE -> List.rev acc
    | rc ->
        ignore (Sqlite3.finalize st);
        check t.db sql rc;
        List.rev acc
  in
  let r = loop [] in
  ignore (Sqlite3.finalize st);
  r

let run_sql t sql args = ignore (query t sql args (fun _ -> ()))

let s_of = function Sqlite3.Data.TEXT s -> s | Sqlite3.Data.NULL -> "" | d -> Sqlite3.Data.to_string_coerce d
let s_opt = function Sqlite3.Data.NULL -> None | d -> Some (s_of d)
let i_of = function Sqlite3.Data.INT i -> Int64.to_int i | d -> int_of_string (s_of d)
let f_opt = function Sqlite3.Data.NULL -> None | Sqlite3.Data.FLOAT f -> Some f | Sqlite3.Data.INT i -> Some (Int64.to_float i) | _ -> None

let json_of d =
  match d with
  | Sqlite3.Data.NULL -> `Null
  | d -> ( match Json.of_string (s_of d) with Ok j -> j | Error _ -> `String (s_of d))

let json_opt d = match json_of d with `Null -> None | j -> Some j
let txt s = Sqlite3.Data.TEXT s
let int i = Sqlite3.Data.INT (Int64.of_int i)
let flt f = Sqlite3.Data.FLOAT f
let opt f = function None -> Sqlite3.Data.NULL | Some x -> f x

let open_ ?path () =
  let path = match path with Some p -> p | None -> default_path () in
  mkdir_p (Filename.dirname path);
  let t = { db = Sqlite3.db_open path; path } in
  exec t "PRAGMA foreign_keys = ON";
  exec t "PRAGMA journal_mode = WAL";
  exec t schema;
  (match query t "SELECT value FROM meta WHERE key='schema_version'" [] (fun g -> s_of (g "value")) with
  | [] -> run_sql t "INSERT INTO meta VALUES ('schema_version', ?)" [ txt (string_of_int schema_version) ]
  | [ v ] when v = string_of_int schema_version -> ()
  | v :: _ -> raise (Db_error (Printf.sprintf "%s: schema v%s, this version expects v%d" path v schema_version)));
  t

let close t = ignore (Sqlite3.db_close t.db)

let bench_of g =
  let language = s_of (g "language") and payload = s_of (g "payload") in
  {
    id = i_of (g "id");
    name = s_of (g "name");
    family = s_of (g "family");
    language;
    params = json_of (g "params");
    expected = Option.bind (s_opt (g "expected")) Families.expected_of_string;
    num_vars = i_of (g "num_vars");
    num_constraints = i_of (g "num_constraints");
    max_width = i_of (g "max_width");
    sha = s_of (g "sha256");
    tags = (match json_of (g "tags") with `List l -> List.filter_map (function `String s -> Some s | _ -> None) l | _ -> []);
    payload;
    problem = lazy (Lang.parse language payload);
  }

let get t name = match query t "SELECT * FROM benchmarks WHERE name=?" [ txt name ] bench_of with b :: _ -> Some b | [] -> None

let digest (p : Lang.problem) = Lang.problem_name p ^ ":" ^ Lang.problem_sha256 p

(* add a benchmark, or return the stored one if it is the same instance *)
let add t ?(family = "custom") ?(params = `Assoc []) ?expected ?(tags = []) (p : Lang.problem) name : (benchmark, string) result =
  let d = digest p in
  let existing = query t "SELECT * FROM benchmarks WHERE name=? OR sha256=?" [ txt name; txt d ] bench_of in
  match List.find_opt (fun b -> b.name = name && b.sha = d) existing with
  | Some b -> Ok b
  | None -> (
      match existing with
      | b :: _ when b.name = name -> Error (Printf.sprintf "benchmark name %s is already used for different content" name)
      | b :: _ -> Error (Printf.sprintf "the same instance is already stored as %s" b.name)
      | [] -> (
          let nv, nc, w = Lang.problem_stats p in
          run_sql t
            {|INSERT INTO benchmarks (name, family, language, params, expected, num_vars,
                num_constraints, max_width, sha256, payload, tags, created_at)
                VALUES (?,?,?,?,?,?,?,?,?,?,?,?)|}
            [
              txt name;
              txt family;
              txt (Lang.problem_name p);
              txt (Json.to_string params);
              opt (fun e -> txt (Families.expected_to_string e)) expected;
              int nv;
              int nc;
              int w;
              txt d;
              txt (Lang.problem_text p);
              txt (Json.to_string (`List (List.map (fun s -> `String s) (List.sort_uniq compare tags))));
              flt (Clock.now ());
            ];
          match get t name with Some b -> Ok b | None -> Error "insert failed"))

let add_generated t ?name (g : Families.generated) =
  add t ~family:g.family ~params:g.params ?expected:g.expected ~tags:g.tags g.problem (Option.value name ~default:g.name)

let remove t name = run_sql t "DELETE FROM benchmarks WHERE name=?" [ txt name ]

type filter = { family : string option; language : string option; max_vars : int option; names : string list; tag : string option }

let all = { family = None; language = None; max_vars = None; names = []; tag = None }

let list ?(filter = all) t =
  let sql = Buffer.create 128 and args = ref [] in
  Buffer.add_string sql "SELECT * FROM benchmarks WHERE 1=1";
  let cond c v =
    Buffer.add_string sql c;
    args := !args @ [ v ]
  in
  Option.iter (fun f -> cond " AND family=?" (txt f)) filter.family;
  Option.iter (fun l -> cond " AND language=?" (txt l)) filter.language;
  Option.iter (fun m -> cond " AND num_vars<=?" (int m)) filter.max_vars;
  if filter.names <> [] then begin
    Buffer.add_string sql (" AND name IN (" ^ String.concat "," (List.map (fun _ -> "?") filter.names) ^ ")");
    args := !args @ List.map txt filter.names
  end;
  Buffer.add_string sql " ORDER BY family, num_vars, num_constraints, name";
  let bs = query t (Buffer.contents sql) !args bench_of in
  match filter.tag with None -> bs | Some tg -> List.filter (fun b -> List.mem tg b.tags) bs

let record_run t (b : benchmark) ~system ~version ~(status : System.Status.t) ?encoding ~config ?verified ~measures ~message ?proof ~search_time
    ?verify_time ?certificate () =
  run_sql t
    {|INSERT INTO runs (benchmark_id, system, system_version, encoding, config, status, verified,
              metrics, message, proof, search_time, verify_time, created_at, certificate)
              VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?)|}
    [
      int b.id;
      txt system;
      txt version;
      opt txt encoding;
      txt (Json.to_string config);
      txt (System.Status.to_string status);
      opt (fun v -> int (if v then 1 else 0)) verified;
      txt (Json.to_string (Measures.to_json measures));
      txt message;
      opt (fun p -> txt (Json.to_string p)) proof;
      flt search_time;
      opt flt verify_time;
      flt (Clock.now ());
      opt (fun c -> txt (Json.to_string c)) certificate;
    ];
  Int64.to_int (Sqlite3.last_insert_rowid t.db)

let run_of ~with_proof g =
  {
    rid = i_of (g "id");
    benchmark = s_of (g "bname");
    system = s_of (g "system");
    system_version = s_of (g "system_version");
    encoding = s_opt (g "encoding");
    config = json_of (g "config");
    status = Option.value (System.Status.of_string (s_of (g "status"))) ~default:System.Status.Error;
    verified = (match g "verified" with Sqlite3.Data.NULL -> None | d -> Some (i_of d = 1));
    measures = (match Measures.of_json (json_of (g "metrics")) with Ok m -> m | Error _ -> Measures.empty);
    message = s_opt (g "message");
    proof = (if with_proof then json_opt (g "proof") else None);
    search_time = f_opt (g "search_time");
    verify_time = f_opt (g "verify_time");
    certificate = (if with_proof then json_opt (g "certificate") else None);
  }

let runs ?system ?benchmark ?(latest_only = false) ?(with_proof = false) t =
  let sql = Buffer.create 128 and args = ref [] in
  Buffer.add_string sql "SELECT r.*, b.name AS bname FROM runs r JOIN benchmarks b ON b.id = r.benchmark_id WHERE 1=1";
  Option.iter
    (fun s ->
      Buffer.add_string sql " AND r.system=?";
      args := !args @ [ txt s ])
    system;
  Option.iter
    (fun s ->
      Buffer.add_string sql " AND b.name=?";
      args := !args @ [ txt s ])
    benchmark;
  Buffer.add_string sql " ORDER BY r.id";
  let rs = query t (Buffer.contents sql) !args (run_of ~with_proof) in
  if not latest_only then rs
  else begin
    let last = Hashtbl.create 64 in
    List.iter (fun r -> Hashtbl.replace last (r.benchmark, r.system) r) rs;
    List.sort (fun a b -> compare a.rid b.rid) (Hashtbl.fold (fun _ r acc -> r :: acc) last [])
  end

let clear_runs ?system t = match system with None -> run_sql t "DELETE FROM runs" [] | Some s -> run_sql t "DELETE FROM runs WHERE system=?" [ txt s ]
