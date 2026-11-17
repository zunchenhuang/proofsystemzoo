(* Truth tables: for each of the 2ⁿ assignments, the index of a clause it
   falsifies. Proof format truth-table/1. *)
open System

let format = "truth-table/1"

(* assignment a (bit v−1 = value of x_v) falsifies the clause iff a land mask = value *)
let pattern (c : Clause.t) =
  List.fold_left
    (fun (mask, value) l ->
      let b = 1 lsl (abs l - 1) in
      (mask lor b, if l < 0 then value lor b else value))
    (0, 0) (Clause.lits c)

type config = unit
type input = Cnf.t
type proof = int array
type lower_bound = Nothing.t

let name = "truth-table"
let version = "0.3"

let info =
  {
    group = "logical";
    order = 0;
    line_type = "assignment";
    primary_metric = "size";
    book = "";
    simulates = [];
    description = "Truth tables: one falsified clause per assignment";
  }

let language = Lang.Cnf
let encoding = None
let params = []
let variants = [ [] ]
let label _ = "TT"
let configure _ = Ok ()
let searches () = true
let parse_text = None

let search () (lim : Limits.t) (cnf : Cnf.t) =
  let n = cnf.num_vars and max_vars = Option.value lim.max_vars ~default:18 in
  if n > max_vars then unknown (Printf.sprintf "%d variables > max_vars=%d" n max_vars)
  else begin
    let pats = Array.map pattern cnf.clauses in
    let masks = Array.map fst pats and values = Array.map snd pats in
    let np = Array.length pats and deadline = Limits.deadline lim in
    let out = Array.make (1 lsl n) 0 in
    let rec go a =
      if a = 1 lsl n then None
      else begin
        if a land 0xffff = 0 then Clock.check deadline;
        let k = ref 0 in
        while !k < np && a land masks.(!k) <> values.(!k) do incr k done;
        if !k = np then Some a
        else begin
          out.(a) <- !k;
          go (a + 1)
        end
      end
    in
    match go 0 with
    | Some a -> model ~witness:(Assignment.of_mask n a) "an assignment satisfies the CNF"
    | None -> refutation ~measures:Measures.(empty |> int "size" (1 lsl n)) out
  end

let verify () (cnf : Cnf.t) (f : proof) =
  let n = cnf.num_vars in
  if n > 30 then Error "truth tables are limited to 30 variables"
  else if Array.length f <> 1 lsl n then Error (Printf.sprintf "need exactly 2^%d entries, got %d" n (Array.length f))
  else begin
    let pats = Array.map pattern cnf.clauses in
    let bad = ref None and a = ref 0 in
    while !bad = None && !a < Array.length f do
      let k = f.(!a) in
      if k < 0 || k >= Array.length pats then bad := Some (Printf.sprintf "assignment %d: bad clause index %d" !a k)
      else begin
        let m, v = pats.(k) in
        if !a land m <> v then bad := Some (Printf.sprintf "assignment %d: clause %d is not falsified" !a k)
      end;
      incr a
    done;
    match !bad with Some s -> Error s | None -> Ok Measures.(empty |> int "size" (Array.length f))
  end

let proof =
  let open Json in
  codec
    (fun f -> E.obj [ ("format", `String format); ("falsified", E.array E.int f) ])
    (fun j ->
      let* () = D.tag "format" format j in
      D.field "falsified" (D.array D.int) j)

let lower_bound = Nothing.codec
let check_lower_bound = Nothing.check
