type ineq = { terms : (int * int) list; rhs : int }
type t = { num_vars : int; ineqs : ineq array; names : (int * string) list }

module IM = Map.Make (Int)

let make_ineq pairs rhs =
  let m =
    List.fold_left
      (fun m (v, c) ->
        if v <= 0 then invalid_arg "Ineq.make_ineq: bad variable";
        IM.update v (fun o -> Some (c + Option.value o ~default:0)) m)
      IM.empty pairs
  in
  { terms = IM.bindings (IM.filter (fun _ c -> c <> 0) m); rhs }

let key q = (List.length q.terms, q.terms, q.rhs)
let cmp_ineq a b = compare (key a) (key b)

let make ?num_vars ?(names = []) qs =
  let qs = Array.of_list (List.sort_uniq cmp_ineq qs) in
  let mx = Array.fold_left (fun m q -> List.fold_left (fun m (v, _) -> max m v) m q.terms) 0 qs in
  let n = Option.value num_vars ~default:mx in
  if mx > n then invalid_arg "Ineq.make: variable exceeds num_vars";
  { num_vars = n; ineqs = qs; names = List.sort compare names }

let holds q a = List.fold_left (fun s (v, c) -> if Assignment.get a v then s + c else s) 0 q.terms >= q.rhs
let eval t a = Array.for_all (fun q -> holds q a) t.ineqs
let max_width t = Array.fold_left (fun m q -> max m (List.length q.terms)) 0 t.ineqs
let terms_text q = String.concat " " (List.map (fun (v, c) -> Printf.sprintf "%+d x%d" c v) q.terms)

let to_text ?(comments = true) t =
  let b = Buffer.create 256 in
  Printf.bprintf b "* #variable= %d #constraint= %d\n" t.num_vars (Array.length t.ineqs);
  if comments then List.iter (fun (v, s) -> Printf.bprintf b "* var %d %s\n" v s) t.names;
  Array.iter (fun q -> Printf.bprintf b "%s >= %d ;\n" (terms_text q) q.rhs) t.ineqs;
  Buffer.contents b

let sha256 t = Sha256.digest (to_text ~comments:false t)
let ineq_to_string q = Printf.sprintf "%s >= %d" (if q.terms = [] then "0" else terms_text q) q.rhs

let of_text (text : string) : (t, string) result =
  let nv = ref None and names = ref [] and qs = ref [] in
  let re_var = Str.regexp "#variable=[ ]*\\([0-9]+\\)" in
  let words s = List.filter (( <> ) "") (String.split_on_char ' ' s) in
  let parse_line raw =
    let line = String.trim raw in
    if line = "" then Ok ()
    else if line.[0] = '*' then begin
      (try
         ignore (Str.search_forward re_var line 0);
         nv := Some (int_of_string (Str.matched_group 1 line))
       with Not_found -> ());
      (match words line with
       | "*" :: "var" :: v :: rest when rest <> [] -> (
           match int_of_string_opt v with Some v -> names := (v, String.concat " " rest) :: !names | None -> ())
       | _ -> ());
      Ok ()
    end
    else
      let line = String.trim (if line.[String.length line - 1] = ';' then String.sub line 0 (String.length line - 1) else line) in
      let find s = try Some (Str.search_forward (Str.regexp_string s) line 0) with Not_found -> None in
      let split i w = (String.sub line 0 i, String.sub line (i + w) (String.length line - i - w)) in
      let rel =
        match (find ">=", find "<=", find "=") with
        | Some i, _, _ -> Some (">=", split i 2)
        | _, Some i, _ -> Some ("<=", split i 2)
        | _, _, Some i -> Some ("=", split i 1)
        | _ -> None
      in
      match rel with
      | None -> Error ("no relation in " ^ raw)
      | Some (op, (lhs, rhs)) -> (
          let toks = Array.of_list (words lhs) in
          if Array.length toks mod 2 = 1 then Error ("bad term list in " ^ raw)
          else
            let term i =
              let x = toks.((2 * i) + 1) in
              match (int_of_string_opt toks.(2 * i), int_of_string_opt (String.sub x 1 (max 0 (String.length x - 1)))) with
              | Some c, Some v when String.length x > 1 && x.[0] = 'x' -> Ok (v, c)
              | _ -> Error ("bad term in " ^ raw)
            in
            match (Seqx.map_result term (List.init (Array.length toks / 2) Fun.id), int_of_string_opt (String.trim rhs)) with
            | Ok terms, Some b ->
                if op = ">=" || op = "=" then qs := make_ineq terms b :: !qs;
                if op = "<=" || op = "=" then qs := make_ineq (List.map (fun (v, c) -> (v, -c)) terms) (-b) :: !qs;
                Ok ()
            | Error e, _ -> Error e
            | _, None -> Error ("bad right-hand side in " ^ raw))
  in
  match Seqx.iter_result parse_line (List.to_seq (String.split_on_char '\n' text)) with
  | Error e -> Error e
  | Ok () -> ( try Ok (make ?num_vars:!nv ~names:!names (List.rev !qs)) with Invalid_argument e -> Error e)
