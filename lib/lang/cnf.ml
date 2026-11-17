type t = { num_vars : int; clauses : Clause.t array; names : (int * string) list }

let make ?num_vars ?(names = []) (cls : Clause.t list) =
  let cs = Array.of_list (List.sort_uniq Clause.compare cls) in
  let mx = Array.fold_left (fun m c -> max m (Clause.max_var c)) 0 cs in
  let n = Option.value num_vars ~default:mx in
  if mx > n then invalid_arg (Printf.sprintf "literal %d exceeds num_vars=%d" mx n);
  { num_vars = n; clauses = cs; names = List.sort compare names }

let of_lists ?num_vars ?names lists = make ?num_vars ?names (List.map Clause.of_list lists)
let num_clauses t = Array.length t.clauses
let max_width t = Array.fold_left (fun m c -> max m (Clause.width c)) 0 t.clauses

let to_dimacs ?(comments = true) t =
  let b = Buffer.create 256 in
  if comments then List.iter (fun (v, s) -> Printf.bprintf b "c var %d %s\n" v s) t.names;
  Printf.bprintf b "p cnf %d %d\n" t.num_vars (num_clauses t);
  Array.iter
    (fun c ->
      Buffer.add_string b (String.concat " " (List.map string_of_int (Clause.lits c)));
      Buffer.add_string b (if Clause.is_empty c then "0\n" else " 0\n"))
    t.clauses;
  Buffer.contents b

let words line = List.filter (( <> ) "") (String.split_on_char ' ' (String.map (fun c -> if c = '\t' then ' ' else c) line))

let of_dimacs (text : string) : (t, string) result =
  let nv = ref None and names = ref [] and cls = ref [] and cur = ref [] in
  let parse_line raw =
    let line = String.trim raw in
    if line = "" || line.[0] = '%' then Ok ()
    else if line.[0] = 'c' then begin
      (match words line with
       | "c" :: "var" :: v :: rest when rest <> [] -> (
           match int_of_string_opt v with Some v -> names := (v, String.concat " " rest) :: !names | None -> ())
       | _ -> ());
      Ok ()
    end
    else if line.[0] = 'p' then
      match words line with
      | [ "p"; "cnf"; n; _ ] -> (
          match int_of_string_opt n with Some n -> nv := Some n; Ok () | None -> Error ("bad problem line: " ^ line))
      | _ -> Error ("bad problem line: " ^ line)
    else
      Seqx.iter_result
        (fun tok ->
          match int_of_string_opt tok with
          | Some 0 -> cls := List.rev !cur :: !cls; cur := []; Ok ()
          | Some l -> cur := l :: !cur; Ok ()
          | None -> Error ("bad literal " ^ tok))
        (List.to_seq (words line))
  in
  match Seqx.iter_result parse_line (List.to_seq (String.split_on_char '\n' text)) with
  | Error e -> Error e
  | Ok () -> (
      if !cur <> [] then cls := List.rev !cur :: !cls;
      match !nv with
      | None -> Error "missing 'p cnf' header"
      | Some n -> ( try Ok (of_lists ~num_vars:n ~names:!names (List.rev !cls)) with Invalid_argument e -> Error e))

let sha256 t = Sha256.digest (to_dimacs ~comments:false t)

let eval t a =
  Array.for_all (fun c -> Array.exists (fun l -> if l > 0 then Assignment.get a l else not (Assignment.get a (-l))) (c : Clause.t :> int array)) t.clauses

let clause_set t =
  let h = Clause.Tbl.create (2 * Array.length t.clauses + 1) in
  Array.iteri (fun i c -> Clause.Tbl.replace h c i) t.clauses;
  h
