(* a minimal test harness: named checks, a summary, a non-zero exit on failure *)
let passed = ref 0
let failed = ref 0

let fail name msg =
  incr failed;
  Printf.printf "FAIL %s: %s\n%!" name msg

let check name b = if b then incr passed else fail name "assertion failed"

let case name f =
  match f () with () -> () | exception e -> fail name ("exception " ^ Printexc.to_string e)

let ok name = function Ok _ -> incr passed | Error e -> fail name e
let err name = function Error _ -> incr passed | Ok _ -> fail name "unexpectedly accepted"

let finish suite =
  Printf.printf "%s: %d checks passed, %d failed\n%!" suite !passed !failed;
  if !failed > 0 then exit 1

let rng seed = Random.State.make [| seed |]
