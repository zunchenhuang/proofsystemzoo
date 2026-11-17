(* Search limits. A typed record instead of free-form key/value pairs: an
   unknown limit is rejected when it is parsed, not silently ignored by the
   system that was supposed to read it.

   [max_size] is each system's own size budget: clauses for saturation,
   lines for tree-like/ordered Resolution, conflicts for CDCL, generators for
   Nullstellensatz, lines for Polynomial Calculus, LP products for
   Sherali–Adams, LP columns for DSOS, Gram-basis size for SoS. *)

type t = {
  time : float option;  (** seconds for the whole search *)
  max_degree : int option;
  max_width : int option;
  max_vars : int option;
  max_size : int option;
}

let none = { time = None; max_degree = None; max_width = None; max_vars = None; max_size = None }
let keys = [ "time"; "max_degree"; "max_width"; "max_vars"; "max_size" ]
let with_time time l = { l with time }
let size (l : t) default = Option.value l.max_size ~default
let deadline (l : t) : Clock.deadline = Clock.after l.time

let set (l : t) (key : string) (value : string) : (t, string) result =
  let int () =
    match int_of_string_opt value with
    | Some i when i >= 0 -> Ok i
    | _ -> Error (Printf.sprintf "limit %s: expected a non-negative integer, got %S" key value)
  in
  match key with
  | "time" | "time_budget" -> (
      match float_of_string_opt value with
      | Some f when f > 0.0 -> Ok { l with time = Some f }
      | _ -> Error (Printf.sprintf "limit time: expected seconds, got %S" value))
  | "max_degree" -> Result.map (fun i -> { l with max_degree = Some i }) (int ())
  | "max_width" -> Result.map (fun i -> { l with max_width = Some i }) (int ())
  | "max_vars" -> Result.map (fun i -> { l with max_vars = Some i }) (int ())
  | "max_size" -> Result.map (fun i -> { l with max_size = Some i }) (int ())
  | k -> Error (Printf.sprintf "unknown limit %S (known: %s)" k (String.concat ", " keys))

let of_pairs (pairs : (string * string) list) : (t, string) result =
  Seqx.fold_result (fun l (k, v) -> set l k v) none (List.to_seq pairs)

(* the limits that are set, for run configurations (time is recorded separately) *)
let to_fields (l : t) : (string * Json.t) list =
  List.filter_map
    (fun (k, v) -> Option.map (fun v -> (k, `Int v)) v)
    [ ("max_degree", l.max_degree); ("max_width", l.max_width); ("max_vars", l.max_vars); ("max_size", l.max_size) ]
