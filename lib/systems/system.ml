(* The contract every proof system implements.

   A system is a module of type [S]. Its types say what it works with:
   [input] is the OCaml type of the language it reads (tied to a {!Lang.t}
   witness, so an instance can only reach [search] and [verify] after it has
   been converted to exactly that type), [proof] and [lower_bound] are its
   own typed objects with JSON codecs (the JSON formats are stable, so other
   tools can produce and check them), and [config] is its parameters, parsed
   once by [configure]. A system without lower-bound certificates uses
   {!Nothing.t}, the empty type: such a certificate cannot be constructed,
   and the checker for it is the empty match. *)

module Status = struct
  type t = Refuted | Satisfiable | Limit | Timeout | Error | Invalid | Unsound | Not_applicable

  let to_string = function
    | Refuted -> "REFUTED"
    | Satisfiable -> "SATISFIABLE"
    | Limit -> "LIMIT"
    | Timeout -> "TIMEOUT"
    | Error -> "ERROR"
    | Invalid -> "INVALID"
    | Unsound -> "UNSOUND"
    | Not_applicable -> "N/A"

  let of_string = function
    | "REFUTED" -> Some Refuted
    | "SATISFIABLE" -> Some Satisfiable
    | "LIMIT" -> Some Limit
    | "TIMEOUT" -> Some Timeout
    | "ERROR" -> Some Error
    | "INVALID" -> Some Invalid
    | "UNSOUND" -> Some Unsound
    | "N/A" -> Some Not_applicable
    | _ -> None

  (* a run that indicates a bug or a broken proof *)
  let is_problem = function Error | Invalid | Unsound -> true | _ -> false
end

type info = {
  group : string; (* logical | algebraic | geometric | semialgebraic *)
  order : int; (* position within the group, roughly by strength *)
  line_type : string;
  primary_metric : string;
  book : string; (* section of Krajíček, Proof Complexity *)
  simulates : string list; (* systems this one p-simulates *)
  description : string;
}

(* what a search found *)
type ('proof, 'lb) outcome =
  | Refutation of { proof : 'proof; measures : Measures.t; lower_bound : 'lb option }
  | Model of { witness : Assignment.t option; measures : Measures.t; message : string }
      (** the input is satisfiable (with a satisfying assignment when the search has one) *)
  | Unknown of { measures : Measures.t; lower_bound : 'lb option; message : string }
      (** a budget ran out; measures may hold partial information such as [degree_lb] *)

module type S = sig
  type config
  type input
  type proof
  type lower_bound

  val name : string
  val version : string
  val info : info
  val language : input Lang.t
  val encoding : string option (* preferred encoding when the input is in another language *)
  val params : Param.spec list
  val variants : (string * string) list list (* parameter settings run by default *)
  val label : Param.env -> string (* short column label in reports *)
  val configure : Param.env -> (config, string) result
  val searches : config -> bool (* false: verifier only *)
  val search : config -> Limits.t -> input -> (proof, lower_bound) outcome
  val proof : proof Json.codec
  val lower_bound : lower_bound Json.codec
  val verify : config -> input -> proof -> (Measures.t, string) result
  val check_lower_bound : config -> input -> lower_bound -> (Measures.t, string) result
  val parse_text : (string -> (proof, string) result) option (* a native text format, e.g. DRAT *)
end

(* An instance: a system with its parameters fixed. *)
module type INSTANCE = sig
  module S : S

  val config : S.config
  val env : Param.env
  val id : string
  val label : string
end

type instance = (module INSTANCE)

let instantiate (module M : S) (given : (string * string) list) : (instance, string) result =
  let ( let* ) = Result.bind in
  let* env = Param.resolve M.params given in
  let* config = M.configure env in
  Ok
    (module struct
      module S = M

      let config = config
      let env = env
      let id = Param.id M.name env
      let label = M.label env
    end : INSTANCE)

let instance_id (module I : INSTANCE) = I.id

(* The empty type, for systems without lower-bound certificates. *)
module Nothing = struct
  type t = |

  let absurd : t -> 'a = function _ -> .
  let codec : t Json.codec = Json.codec absurd (fun _ -> Error "this system has no lower-bound certificates")
  let check _ _ (x : t) = absurd x
end

(* ------------------------------------------------------------ outcomes *)

let outcome_codec (pc : 'p Json.codec) (lc : 'l Json.codec) : ('p, 'l) outcome Json.codec =
  let open Json in
  let lb = function None -> `Null | Some l -> lc.encode l in
  let encode = function
    | Refutation r ->
        E.obj [ ("kind", `String "refutation"); ("proof", pc.encode r.proof); ("measures", Measures.to_json r.measures); ("lower_bound", lb r.lower_bound) ]
    | Model r ->
        E.obj
          [
            ("kind", `String "model");
            ("witness", E.nullable Assignment.codec.encode r.witness);
            ("measures", Measures.to_json r.measures);
            ("message", `String r.message);
          ]
    | Unknown r ->
        E.obj [ ("kind", `String "unknown"); ("measures", Measures.to_json r.measures); ("lower_bound", lb r.lower_bound); ("message", `String r.message) ]
  in
  let decode j =
    let* kind = D.field "kind" D.string j in
    let* measures = D.field "measures" Measures.of_json j in
    match kind with
    | "refutation" ->
        let* proof = D.field "proof" pc.decode j in
        let+ lower_bound = D.field_opt "lower_bound" lc.decode j in
        Refutation { proof; measures; lower_bound }
    | "model" ->
        let* witness = D.field_opt "witness" Assignment.codec.decode j in
        let+ message = D.field "message" D.string j in
        Model { witness; measures; message }
    | "unknown" ->
        let* lower_bound = D.field_opt "lower_bound" lc.decode j in
        let+ message = D.field "message" D.string j in
        Unknown { measures; lower_bound; message }
    | k -> error "unknown outcome kind %S" k
  in
  codec encode decode

(* ------------------------------------------------------------ helpers *)

let refutation ?lower_bound ?(measures = Measures.empty) proof = Refutation { proof; measures; lower_bound }
let model ?witness ?(measures = Measures.empty) message = Model { witness; measures; message }
let unknown ?lower_bound ?(measures = Measures.empty) message = Unknown { measures; lower_bound; message }
let budget_message = "time budget exhausted"

(* "rule" objects of line-based proof formats *)
let rule_of j = Json.D.field "rule" Json.D.string j

let check b fmt = Printf.ksprintf (fun s -> if b then Ok () else Error s) fmt
