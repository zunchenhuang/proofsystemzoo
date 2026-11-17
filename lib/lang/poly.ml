type mono = int list
type poly = (mono * int) list
type t = { num_vars : int; polys : poly array; names : (int * string) list }

let mono_key (m : mono) = (List.length m, m)

let make_poly (terms : (int list * int) list) : poly =
  let tbl = Hashtbl.create 8 in
  List.iter
    (fun (m, c) ->
      let m = List.sort_uniq compare m in
      Hashtbl.replace tbl m (c + Option.value (Hashtbl.find_opt tbl m) ~default:0))
    terms;
  Hashtbl.fold (fun m c acc -> if c <> 0 then (m, c) :: acc else acc) tbl []
  |> List.sort (fun (a, _) (b, _) -> compare (mono_key a) (mono_key b))

let terms (f : poly) = f
let degree (f : poly) = List.fold_left (fun d (m, _) -> max d (List.length m)) 0 f
let vars (f : poly) = List.sort_uniq compare (List.concat_map fst f)
let cmp_poly a b = compare (degree a, a) (degree b, b)

let make ?num_vars ?(names = []) (ps : poly list) =
  let ps = Array.of_list (List.sort_uniq cmp_poly (List.filter (( <> ) []) ps)) in
  let mx = Array.fold_left (fun m f -> List.fold_left max m (vars f)) 0 ps in
  let n = Option.value num_vars ~default:mx in
  if mx > n then invalid_arg "Poly.make: variable exceeds num_vars";
  { num_vars = n; polys = ps; names = List.sort compare names }

let eval_poly (f : poly) a = List.fold_left (fun s (m, c) -> if List.for_all (Assignment.get a) m then s + c else s) 0 f
let eval t a = Array.for_all (fun f -> eval_poly f a = 0) t.polys
let max_degree t = Array.fold_left (fun d f -> max d (degree f)) 0 t.polys

let to_text ?(comments = true) t =
  let b = Buffer.create 256 in
  Printf.bprintf b "p %d %d\n" t.num_vars (Array.length t.polys);
  if comments then List.iter (fun (v, s) -> Printf.bprintf b "c var %d %s\n" v s) t.names;
  Array.iter
    (fun f ->
      Buffer.add_string b
        (String.concat " " (List.map (fun (m, c) -> string_of_int c ^ String.concat "" (List.map (fun v -> "*x" ^ string_of_int v) m)) f));
      Buffer.add_string b " = 0\n")
    t.polys;
  Buffer.contents b

let sha256 t = Sha256.digest (to_text ~comments:false t)

let of_text (text : string) : (t, string) result =
  let nv = ref None and names = ref [] and ps = ref [] in
  let words s = List.filter (( <> ) "") (String.split_on_char ' ' s) in
  let parse_line raw =
    let line = String.trim raw in
    if line = "" then Ok ()
    else if line.[0] = 'c' then begin
      (match words line with
       | "c" :: "var" :: v :: rest when rest <> [] -> (
           match int_of_string_opt v with Some v -> names := (v, String.concat " " rest) :: !names | None -> ())
       | _ -> ());
      Ok ()
    end
    else if line.[0] = 'p' then
      match words line with
      | _ :: n :: _ -> (match int_of_string_opt n with Some n -> nv := Some n; Ok () | None -> Error ("bad header " ^ line))
      | _ -> Error ("bad header " ^ line)
    else
      let body = List.hd (String.split_on_char '=' line) in
      let term tok =
        match String.split_on_char '*' tok with
        | c :: xs -> (
            match int_of_string_opt c with
            | None -> Error ("bad coefficient in " ^ tok)
            | Some c ->
                Result.map
                  (fun vs -> (vs, c))
                  (Seqx.map_result
                     (fun x ->
                       match int_of_string_opt (String.sub x 1 (max 0 (String.length x - 1))) with
                       | Some v when String.length x > 1 && x.[0] = 'x' && v >= 1 -> Ok v
                       | _ -> Error ("bad variable " ^ x))
                     xs))
        | [] -> Error "empty term"
      in
      Result.map (fun ts -> ps := make_poly ts :: !ps) (Seqx.map_result term (words body))
  in
  match Seqx.iter_result parse_line (List.to_seq (String.split_on_char '\n' text)) with
  | Error e -> Error e
  | Ok () -> ( try Ok (make ?num_vars:!nv ~names:!names (List.rev !ps)) with Invalid_argument e -> Error e)
