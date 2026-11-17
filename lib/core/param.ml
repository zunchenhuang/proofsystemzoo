(* Parameters of a proof-system family, e.g. the field of Nullstellensatz or
   the cone of Sum-of-Squares. A spec validates and normalises a value; an
   environment is complete (defaults filled in), normalised and sorted, so
   equal environments name equal instances. *)

type spec = { key : string; default : string; doc : string; normalize : string -> (string, string) result }
type env = (string * string) list

let prime ?(doc = "a prime p: the field GF(p)") ~key ~default () =
  let normalize s =
    match int_of_string_opt (String.trim s) with
    | Some p when Num.is_prime p && p < 1 lsl 30 -> Ok (string_of_int p)
    | _ -> Error (Printf.sprintf "%s=%s is not a prime below 2^30" key s)
  in
  { key; default = string_of_int default; doc; normalize }

let choice ?(doc = "") ~key ~default values =
  let normalize s =
    let s = String.trim s in
    if List.mem s values then Ok s
    else Error (Printf.sprintf "%s=%s: expected one of %s" key s (String.concat ", " values))
  in
  { key; default; doc = (if doc = "" then String.concat " | " values else doc); normalize }

let resolve (specs : spec list) (given : (string * string) list) : (env, string) result =
  let ( let* ) = Result.bind in
  let* () =
    match List.find_opt (fun (k, _) -> not (List.exists (fun s -> s.key = k) specs)) given with
    | Some (k, _) ->
        Error
          (Printf.sprintf "unknown parameter %s%s" k
             (if specs = [] then " (this system has no parameters)"
              else " (known: " ^ String.concat ", " (List.map (fun s -> s.key) specs) ^ ")"))
    | None -> Ok ()
  in
  let* env =
    Seqx.map_result
      (fun s ->
        let v = Option.value (List.assoc_opt s.key given) ~default:s.default in
        Result.map (fun v -> (s.key, v)) (s.normalize v))
      specs
  in
  Ok (List.sort compare env)

let get (env : env) key = match List.assoc_opt key env with Some v -> v | None -> invalid_arg ("Param.get " ^ key)
let get_int env key = int_of_string (get env key)

let id name (env : env) =
  if env = [] then name else name ^ "[" ^ String.concat "," (List.map (fun (k, v) -> k ^ "=" ^ v) env) ^ "]"

(* "name" or "name[k=v,...]" *)
let parse_id (s : string) : (string * (string * string) list, string) result =
  let s = String.trim s in
  match String.index_opt s '[' with
  | None -> Ok (s, [])
  | Some i ->
      if s.[String.length s - 1] <> ']' then Error ("bad system id " ^ s)
      else
        let inner = String.sub s (i + 1) (String.length s - i - 2) in
        let parts = List.filter (fun p -> String.trim p <> "") (String.split_on_char ',' inner) in
        Result.map
          (fun kvs -> (String.sub s 0 i, kvs))
          (Seqx.map_result
             (fun kv ->
               match String.split_on_char '=' kv with
               | [ k; v ] -> Ok (String.trim k, String.trim v)
               | _ -> Error ("bad parameter " ^ kv))
             parts)
