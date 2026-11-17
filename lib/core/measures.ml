(* Measures of a proof or a search: proof size, degree, width, rank, the
   strategy that found it, certified lower bounds, ... A finite map from
   names to typed values; serialised with sorted keys. *)

module SM = Map.Make (String)

type value = Int of int | Big of Z.t | Text of string | Flag of bool
type t = value SM.t

let empty : t = SM.empty
let int k v (m : t) : t = SM.add k (Int v) m
let big k v (m : t) : t = SM.add k (if Z.fits_int v then Int (Z.to_int v) else Big v) m
let text k v (m : t) : t = SM.add k (Text v) m
let flag k v (m : t) : t = SM.add k (Flag v) m
let remove k (m : t) : t = SM.remove k m

(* right-biased: values in [b] win *)
let union (a : t) (b : t) : t = SM.union (fun _ _ y -> Some y) a b
let of_list l : t = List.fold_left (fun m (k, v) -> SM.add k v m) SM.empty l
let to_list (m : t) = SM.bindings m
let find k (m : t) = SM.find_opt k m
let find_int k (m : t) = match SM.find_opt k m with Some (Int i) -> Some i | _ -> None
let find_flag k (m : t) = match SM.find_opt k m with Some (Flag b) -> b | _ -> false
let mem k (m : t) = SM.mem k m
let is_empty (m : t) = SM.is_empty m

let value_to_json = function
  | Int i -> `Int i
  | Big z -> Json.E.z z
  | Text s -> `String s
  | Flag b -> `Bool b

let value_to_string = function
  | Int i -> string_of_int i
  | Big z -> Z.to_string z
  | Text s -> s
  | Flag b -> string_of_bool b

let to_json (m : t) : Json.t = `Assoc (List.map (fun (k, v) -> (k, value_to_json v)) (SM.bindings m))

let of_json : t Json.decoder = function
  | `Assoc l ->
      Seqx.fold_result
        (fun m (k, v) ->
          match v with
          | `Int i -> Ok (SM.add k (Int i) m)
          | `Intlit s -> Ok (SM.add k (Big (Z.of_string s)) m)
          | `String s -> Ok (SM.add k (Text s) m)
          | `Bool b -> Ok (SM.add k (Flag b) m)
          | `Float f -> Ok (SM.add k (Text (string_of_float f)) m)
          | _ -> Json.error "measure %s: unsupported value" k)
        SM.empty (List.to_seq l)
  | `Null -> Ok SM.empty
  | _ -> Error "measures: expected an object"

let codec = Json.codec to_json of_json

(* a compact rendering of the measures most people look at *)
let summary ?(keys = [ "size"; "degree"; "width"; "rank" ]) (m : t) =
  List.filter_map (fun k -> Option.map (fun v -> (k, v)) (find k m)) keys
  |> List.map (fun (k, v) -> k ^ "=" ^ value_to_string v)
  |> String.concat " "
