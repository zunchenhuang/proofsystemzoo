(* Reports: the benchmark × system matrix and the map of the zoo.

   A cell shows the system's primary measure for a verified refutation,
   starred when a checked lower-bound certificate matches it (the value is
   then a certified minimum); "≥k" when a budget ran out after
   establishing k, starred when k is certified; "sat" with a star for a
   satisfiable benchmark with a checked witness; otherwise the status. *)
open System

let short = function
  | Status.Refuted -> "ref"
  | Satisfiable -> "sat"
  | Limit -> "limit"
  | Timeout -> "t/o"
  | Error -> "err"
  | Invalid -> "INVALID"
  | Unsound -> "UNSOUND"
  | Not_applicable -> "n/a"

let cell metric (r : Store.run option) =
  match r with
  | None -> "·"
  | Some r -> (
      let cert = Measures.find_int (metric ^ "_lb_certified") r.measures in
      if r.status = Status.Refuted && r.verified = Some true then
        match Measures.find metric r.measures with
        | None -> "✓"
        | Some v -> (
            let s = Measures.value_to_string v in
            match (cert, v) with Some c, Measures.Int x when c >= x -> s ^ "*" | _ -> s)
      else
        let lb = Measures.find_int (metric ^ "_lb") r.measures in
        match (r.status, lb, cert) with
        | (Status.Limit | Status.Timeout), _, _ when lb <> None || cert <> None ->
            let best = max (Option.value lb ~default:0) (Option.value cert ~default:0) in
            Printf.sprintf "≥%d%s" best (if Option.value cert ~default:(-1) >= best then "*" else "")
        | Status.Satisfiable, _, _ when Measures.find_flag "witness" r.measures -> "sat*"
        | s, _, _ -> short s)

type column = { label : string; id : string; metric : string; language : Lang.any }
type table = { header : string list; rows : string list list; legend : column list }

let column_of (inst : instance) =
  let (module I : INSTANCE) = inst in
  { label = I.label; id = I.id; metric = I.S.info.primary_metric; language = Lang.Any I.S.language }

(* default instances first, then any other instance that has runs *)
let columns ?only (st : Store.t) =
  let defaults = List.map column_of (Registry.default_instances ()) in
  let seen = List.sort_uniq compare (List.map (fun (r : Store.run) -> r.system) (Store.runs st)) in
  let extra =
    List.filter_map
      (fun id -> if List.exists (fun c -> c.id = id) defaults then None else Result.to_option (Result.map column_of (Registry.instance id)))
      seen
  in
  let cols = defaults @ extra in
  match only with None -> cols | Some ids -> List.filter (fun c -> List.mem c.id ids || List.mem c.label ids) cols

let matrix ?only (st : Store.t) (benches : Store.benchmark list) : table =
  let cols = columns ?only st in
  let latest = Hashtbl.create 256 in
  List.iter (fun (r : Store.run) -> Hashtbl.replace latest (r.benchmark, r.system) r) (Store.runs ~latest_only:true st);
  let rows =
    List.map
      (fun (b : Store.benchmark) ->
        let lang = Lang.of_name b.language in
        b.name
        :: (match b.expected with Some e -> Families.expected_to_string e | None -> "?")
        :: List.map
             (fun c ->
               match Hashtbl.find_opt latest (b.name, c.id) with
               | Some r -> cell c.metric (Some r)
               | None -> ( match lang with Some l when not (Encodings.reachable l c.language) -> "n/a" | _ -> "·"))
             cols)
      benches
  in
  { header = "benchmark" :: "expect" :: List.map (fun c -> c.label) cols; rows; legend = cols }

(* display width of a UTF-8 string *)
let width s =
  let n = ref 0 in
  String.iter (fun ch -> if Char.code ch land 0xC0 <> 0x80 then incr n) s;
  !n

let pad s w = s ^ String.make (max 0 (w - width s)) ' '

let render_text (t : table) =
  let all = t.header :: t.rows in
  let ncol = List.length t.header in
  let w = Array.make ncol 0 in
  List.iter (List.iteri (fun i s -> w.(i) <- max w.(i) (width s))) all;
  let line r = String.concat "  " (List.mapi (fun i s -> pad s w.(i)) r) in
  let b = Buffer.create 4096 in
  Buffer.add_string b (line t.header ^ "\n");
  Buffer.add_string b (String.concat "  " (Array.to_list (Array.map (fun x -> String.make x '-') w)) ^ "\n");
  List.iter (fun r -> Buffer.add_string b (line r ^ "\n")) t.rows;
  Buffer.add_string b "\n";
  List.iter (fun c -> Buffer.add_string b (Printf.sprintf "  %-6s %s (%s)\n" c.label c.id c.metric)) t.legend;
  Buffer.add_string b "\n  n* certified minimum (checked lower-bound certificate)   ≥k* budget ran out, k certified\n";
  Buffer.add_string b "  sat* satisfiable, witness checked   n/a no encoding applies   · not run\n";
  Buffer.contents b

let render_md (t : table) =
  let row r = "| " ^ String.concat " | " r ^ " |" in
  String.concat "\n" (row t.header :: row (List.map (fun _ -> "---") t.header) :: List.map row t.rows) ^ "\n"

let render_csv (t : table) =
  let q s = if String.exists (fun c -> c = ',' || c = '"') s then "\"" ^ String.concat "\"\"" (String.split_on_char '"' s) ^ "\"" else s in
  String.concat "\n" (List.map (fun r -> String.concat "," (List.map q r)) (t.header :: t.rows)) ^ "\n"

(* ------------------------------------------------------------ the zoo *)
let zoo () =
  let b = Buffer.create 4096 in
  let label (module S : System.S) =
    let params = String.concat ", " (List.map (fun (p : Param.spec) -> p.key ^ "=" ^ p.default) S.params) in
    S.name ^ if params = "" then "" else "[" ^ params ^ "]"
  in
  let w = 2 + List.fold_left (fun m s -> max m (width (label s))) 0 (Registry.systems ()) in
  List.iter
    (fun group ->
      let members = List.filter (fun (module S : System.S) -> S.info.group = group) (Registry.systems ()) in
      if members <> [] then begin
        Printf.bprintf b "%s\n" (String.uppercase_ascii group);
        List.iter
          (fun (module S : System.S) ->
            Printf.bprintf b "  %s%s\n" (pad (label (module S)) w) S.info.description;
            Printf.bprintf b "  %s lines: %s; measure: %s; reads %s%s%s\n" (String.make (w - 1) ' ') S.info.line_type S.info.primary_metric (Lang.name S.language)
              (match S.encoding with Some e -> " (via " ^ e ^ ")" | None -> "")
              (if S.info.book = "" then "" else "; Krajíček §" ^ S.info.book);
            if S.info.simulates <> [] then Printf.bprintf b "  %s p-simulates: %s\n" (String.make (w - 1) ' ') (String.concat ", " S.info.simulates))
          members;
        Buffer.add_char b '\n'
      end)
    Registry.group_order;
  Buffer.contents b
