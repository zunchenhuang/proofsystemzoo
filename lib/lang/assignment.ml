(* Total assignments to variables 1..n (true = 1). Serialised as
   {"assignment": {"1": true, "2": false, ...}}. *)

type t = bool array (* index 0 unused *)

let make n (f : int -> bool) : t = Array.init (n + 1) (fun v -> v > 0 && f v)
let get (a : t) v = v > 0 && v < Array.length a && a.(v)
let num_vars (a : t) = Array.length a - 1
let of_mask n mask : t = make n (fun v -> (mask lsr (v - 1)) land 1 = 1)

(* all 2^n assignments, as a lazy sequence (for brute force on tiny instances) *)
let all n : t Seq.t = Seq.map (of_mask n) (Seqx.range 0 (1 lsl n))

let codec : t Json.codec =
  let encode a =
    `Assoc [ ("assignment", `Assoc (List.init (num_vars a) (fun i -> (string_of_int (i + 1), `Bool a.(i + 1))))) ]
  in
  let decode j =
    let open Json in
    let* l = D.field "assignment" D.assoc j in
    let* pairs =
      Seqx.map_result
        (fun (k, v) ->
          match (int_of_string_opt k, v) with
          | Some x, `Bool b when x >= 1 -> Ok (x, b)
          | _ -> error "bad assignment entry %S" k)
        l
    in
    let n = List.fold_left (fun m (x, _) -> max m x) 0 pairs in
    let a = Array.make (n + 1) false in
    List.iter (fun (x, b) -> a.(x) <- b) pairs;
    Ok a
  in
  Json.codec encode decode
