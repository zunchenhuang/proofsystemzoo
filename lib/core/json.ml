(* Typed JSON codecs.

   Proofs, certificates, measures and configurations cross process and
   storage boundaries as JSON. Every such type has a codec: an encoder to
   JSON and a decoder back that returns a [result], so malformed input is an
   ordinary [Error] with a path to the offending value, never an exception
   and never a partially-checked value. *)

type t = Yojson.Safe.t

type 'a decoder = t -> ('a, string) result
type 'a codec = { encode : 'a -> t; decode : 'a decoder }

let ( let* ) = Result.bind
let ( let+ ) r f = Result.map f r
let error fmt = Printf.ksprintf (fun s -> Error s) fmt

let to_string (j : t) = Yojson.Safe.to_string j
let of_string (s : string) : (t, string) result =
  try Ok (Yojson.Safe.from_string s) with Yojson.Json_error e -> Error ("invalid JSON: " ^ e)

let short (j : t) =
  let s = to_string j in
  if String.length s > 40 then String.sub s 0 37 ^ "..." else s

let in_context ctx r = Result.map_error (fun e -> ctx ^ ": " ^ e) r

(* ------------------------------------------------------------- decoders *)
module D = struct
  let int : int decoder = function
    | `Int i -> Ok i
    | `Intlit s -> ( match int_of_string_opt s with Some i -> Ok i | None -> error "integer out of range: %s" s)
    | j -> error "expected an integer, got %s" (short j)

  let z : Z.t decoder = function
    | `Int i -> Ok (Z.of_int i)
    | `Intlit s | `String s -> ( try Ok (Z.of_string s) with _ -> error "bad integer %S" s)
    | j -> error "expected an integer, got %s" (short j)

  (* rationals are strings "p/q" or "p" (integers are accepted too) *)
  let q : Q.t decoder = function
    | `String s -> (
        match Q.of_string s with
        | x when Z.sign (Q.den x) > 0 -> Ok x
        | _ -> error "bad rational %S" s
        | exception _ -> error "bad rational %S" s)
    | `Int i -> Ok (Q.of_int i)
    | `Intlit s -> ( try Ok (Q.of_string s) with _ -> error "bad rational %S" s)
    | j -> error "expected a rational, got %s" (short j)

  let float : float decoder = function
    | `Float f -> Ok f
    | `Int i -> Ok (float_of_int i)
    | j -> error "expected a number, got %s" (short j)

  let string : string decoder = function `String s -> Ok s | j -> error "expected a string, got %s" (short j)
  let bool : bool decoder = function `Bool b -> Ok b | j -> error "expected a boolean, got %s" (short j)

  let list (d : 'a decoder) : 'a list decoder = function
    | `List l ->
        let rec go i acc = function
          | [] -> Ok (List.rev acc)
          | x :: r -> ( match d x with Ok y -> go (i + 1) (y :: acc) r | Error e -> error "[%d]: %s" i e)
        in
        go 0 [] l
    | j -> error "expected a list, got %s" (short j)

  let array d j = Result.map Array.of_list (list d j)

  let pair (da : 'a decoder) (db : 'b decoder) : ('a * 'b) decoder = function
    | `List [ a; b ] ->
        let* x = in_context "[0]" (da a) in
        let+ y = in_context "[1]" (db b) in
        (x, y)
    | j -> error "expected a pair, got %s" (short j)

  let nullable (d : 'a decoder) : 'a option decoder = function `Null -> Ok None | j -> Result.map Option.some (d j)

  let assoc : (string * t) list decoder = function
    | `Assoc l -> Ok l
    | j -> error "expected an object, got %s" (short j)

  let field (k : string) (d : 'a decoder) : 'a decoder = function
    | `Assoc l -> ( match List.assoc_opt k l with Some v -> in_context k (d v) | None -> error "missing field %S" k)
    | j -> error "expected an object, got %s" (short j)

  let field_opt (k : string) (d : 'a decoder) : 'a option decoder = function
    | `Assoc l -> (
        match List.assoc_opt k l with None | Some `Null -> Ok None | Some v -> in_context k (Result.map Option.some (d v)))
    | j -> error "expected an object, got %s" (short j)

  (* the "format" tag of a proof object *)
  let tag (k : string) (expected : string) : unit decoder =
   fun j ->
    let* s = field k string j in
    if s = expected then Ok () else error "expected %s %S, got %S" k expected s
end

(* ------------------------------------------------------------- encoders *)
module E = struct
  let int i : t = `Int i
  let z (x : Z.t) : t = if Z.fits_int x then `Int (Z.to_int x) else `Intlit (Z.to_string x)
  let q (x : Q.t) : t = `String (Q.to_string x)
  let float f : t = `Float f
  let string s : t = `String s
  let bool b : t = `Bool b
  let list f l : t = `List (List.map f l)
  let array f a : t = `List (Array.to_list (Array.map f a))
  let pair fa fb (a, b) : t = `List [ fa a; fb b ]
  let ints l : t = list int l
  let nullable f = function None -> `Null | Some x -> f x
  let obj (fields : (string * t) list) : t = `Assoc fields
end

(* ------------------------------------------------------------- codecs *)
let codec encode decode = { encode; decode }
let int = codec E.int D.int
let z = codec E.z D.z
let q = codec E.q D.q
let string = codec E.string D.string
let bool = codec E.bool D.bool
let list c = codec (E.list c.encode) (D.list c.decode)
let pair a b = codec (E.pair a.encode b.encode) (D.pair a.decode b.decode)

(* round trip through text, as across a process boundary *)
let roundtrip (c : 'a codec) (x : 'a) : ('a, string) result =
  let* j = of_string (to_string (c.encode x)) in
  c.decode j
