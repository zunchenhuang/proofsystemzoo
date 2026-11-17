(* Wall-clock deadlines for searches. A deadline is an absolute time, or
   [None] for "no limit". Long computations poll it and raise [Timeout],
   which each system turns into an honest "unknown" outcome. *)

type deadline = float option

exception Timeout

let now = Unix.gettimeofday
let after (seconds : float option) : deadline = Option.map (fun s -> now () +. s) seconds
let expired (d : deadline) = match d with None -> false | Some t -> now () > t
let check (d : deadline) = if expired d then raise Timeout
let remaining (d : deadline) = Option.map (fun t -> Float.max 0.0 (t -. now ())) d

(* a fraction of the remaining time, as a new deadline *)
let share (d : deadline) (fraction : float) : deadline =
  Option.map (fun t -> now () +. (fraction *. Float.max 0.0 (t -. now ()))) d

(* [time f] = (result, seconds) *)
let time f =
  let t0 = now () in
  let r = f () in
  (r, now () -. t0)
