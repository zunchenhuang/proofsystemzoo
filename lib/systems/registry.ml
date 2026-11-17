(* All systems, as first-class modules, ordered by group and roughly by
   strength; instance lookup by identifier ("name" or "name[k=v,...]"). *)

let group_order = [ "logical"; "algebraic"; "geometric"; "semialgebraic" ]

let zoo_key (module S : System.S) =
  let rec idx i = function [] -> List.length group_order | g :: r -> if g = S.info.group then i else idx (i + 1) r in
  (idx 0 group_order, S.info.group, S.info.order, S.name)

let sort l = List.sort (fun a b -> compare (zoo_key a) (zoo_key b)) l
let name_of (module S : System.S) = S.name

let builtin : (module System.S) list =
  [
    (module Truth_table);
    (module Resolution.Tree);
    (module Resolution.Ordered);
    (module Resolution.Dag);
    (module Drat);
    (module Nullstellensatz);
    (module Polycalc.Pc);
    (module Polycalc.Pcr);
    (module Cutting_planes);
    (module Sos);
    (module Sherali_adams);
  ]

let all = ref (sort builtin)

(* add a system defined outside this library *)
let register (s : (module System.S)) =
  if List.exists (fun x -> name_of x = name_of s) !all then invalid_arg ("system already registered: " ^ name_of s);
  all := sort (s :: !all)

let systems () = !all
let find name = List.find_opt (fun s -> name_of s = name) !all

let instance (ident : string) : (System.instance, string) result =
  match Param.parse_id ident with
  | Error e -> Error e
  | Ok (name, given) -> (
      match find name with
      | None -> Error (Printf.sprintf "unknown system %s (known: %s)" name (String.concat ", " (List.map name_of !all)))
      | Some s -> Result.map_error (fun e -> name ^ ": " ^ e) (System.instantiate s given))

let variants (module S : System.S) : System.instance list =
  List.filter_map (fun v -> Result.to_option (System.instantiate (module S) v)) S.variants

let default_instances () = List.concat_map variants !all
