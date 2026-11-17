(* Benchmark families: deterministic generators. A family name plus its
   parameters always reproduces the same instance (and content hash). *)

type expected = Sat | Unsat

let expected_to_string = function Sat -> "SAT" | Unsat -> "UNSAT"
let expected_of_string = function "SAT" -> Some Sat | "UNSAT" -> Some Unsat | _ -> None

type generated = {
  name : string;
  family : string;
  params : Json.t;
  problem : Lang.problem;
  expected : expected option;
  tags : string list;
}

(* ------------------------------------------------------------ pigeonhole *)
let php ?m n =
  let m = Option.value m ~default:(n + 1) in
  if n < 1 || m < 1 then invalid_arg "php: need n, m >= 1";
  let var i j = (i * n) + j + 1 in
  let names = List.concat (List.init m (fun i -> List.init n (fun j -> (var i j, Printf.sprintf "p%d_%d" i j)))) in
  let pigeons = List.init m (fun i -> List.init n (fun j -> var i j)) in
  let holes =
    List.concat_map
      (fun j -> Seqx.combinations (Array.init m Fun.id) 2 |> Seq.map (fun ik -> List.map (fun i -> - var i j) ik) |> List.of_seq)
      (List.init n Fun.id)
  in
  {
    name = Printf.sprintf "php-%d-%d" m n;
    family = "php";
    params = `Assoc [ ("m", `Int m); ("n", `Int n) ];
    problem = Lang.Problem (Lang.Cnf, Cnf.of_lists ~num_vars:(m * n) ~names (pigeons @ holes));
    expected = Some (if m > n then Unsat else Sat);
    tags = "pigeonhole" :: (if m <= n then [ "control" ] else []);
  }

(* --------------------------------------------------------------- Tseitin *)
type size = One of int | Two of int * int

let graph kind size =
  match (kind, size) with
  | "cycle", One n ->
      if n < 3 then invalid_arg "tseitin: a cycle needs >= 3 vertices";
      (n, List.init n (fun i -> (i, (i + 1) mod n)))
  | "grid", sz ->
      let r, c = match sz with One k -> (k, k) | Two (r, c) -> (r, c) in
      let idx a b = (a * c) + b in
      let edges =
        List.concat
          (List.init r (fun a ->
               List.concat
                 (List.init c (fun b ->
                      (if b + 1 < c then [ (idx a b, idx a (b + 1)) ] else []) @ if a + 1 < r then [ (idx a b, idx (a + 1) b) ] else []))))
      in
      (r * c, edges)
  | "complete", One n -> (n, List.of_seq (Seq.map (function [ a; b ] -> (a, b) | _ -> assert false) (Seqx.combinations (Array.init n Fun.id) 2)))
  | k, _ -> invalid_arg ("tseitin: unknown graph kind " ^ k ^ " (cycle | grid | complete)")

(* one variable per edge; at each vertex the XOR of incident edges equals its charge *)
let tseitin_cnf nv edges charges =
  let incident = Array.make nv [] in
  List.iteri (fun k (u, w) -> incident.(u) <- incident.(u) @ [ k + 1 ]; incident.(w) <- incident.(w) @ [ k + 1 ]) edges;
  let names = List.mapi (fun k (u, w) -> (k + 1, Printf.sprintf "e%d_%d" u w)) edges in
  let clauses =
    List.concat
      (List.mapi
         (fun v evars ->
           let c = Option.value (List.assoc_opt v charges) ~default:0 land 1 in
           let d = List.length evars in
           List.filter_map
             (fun bits ->
               let ones = List.length (List.filter (fun i -> (bits lsr i) land 1 = 1) (List.init d Fun.id)) in
               if ones mod 2 <> c then Some (List.mapi (fun i x -> if (bits lsr i) land 1 = 0 then x else -x) evars) else None)
             (List.init (1 lsl d) Fun.id))
         (Array.to_list incident))
  in
  Cnf.of_lists ~num_vars:(List.length edges) ~names clauses

let tseitin ?(odd = true) kind size =
  let nv, edges = graph kind size in
  let charges = if odd then [ (0, 1) ] else [ (0, 1); (nv - 1, 1) ] in
  let sz, jsize = match size with One k -> (string_of_int k, `Int k) | Two (r, c) -> (Printf.sprintf "%dx%d" r c, `List [ `Int r; `Int c ]) in
  {
    name = Printf.sprintf "tseitin-%s-%s%s" kind sz (if odd then "" else "-even");
    family = "tseitin";
    params = `Assoc [ ("graph", `String kind); ("odd", `Bool odd); ("size", jsize) ];
    problem = Lang.Problem (Lang.Cnf, tseitin_cnf nv edges charges);
    expected = Some (if odd then Unsat else Sat);
    tags = [ "tseitin"; kind ] @ if odd then [] else [ "control" ];
  }

(* ---------------------------------------------------------------- parity *)
let parity n =
  if n < 1 then invalid_arg "parity: need n >= 1";
  let t = (2 * (n / 2)) + 1 in
  let vs = List.init n (fun i -> i + 1) in
  let s = Ineq.make ~num_vars:n [ Ineq.make_ineq (List.map (fun v -> (v, 2)) vs) t; Ineq.make_ineq (List.map (fun v -> (v, -2)) vs) (-t) ] in
  { name = Printf.sprintf "parity-%d" n; family = "parity"; params = `Assoc [ ("n", `Int n) ]; problem = Lang.Problem (Lang.Ineq, s); expected = Some Unsat; tags = [ "ilp" ] }

(* ------------------------------------------------------------- registry *)
type family = { fname : string; doc : string; generate : (string * Json.t) list -> (generated, string) result }

let guard f = try Ok (f ()) with Invalid_argument e -> Error e

let families =
  let open Json in
  let int k ps = match List.assoc_opt k ps with Some j -> in_context k (D.int j) | None -> error "missing parameter %s" k in
  let int_opt k ps = match List.assoc_opt k ps with Some j -> Result.map Option.some (in_context k (D.int j)) | None -> Ok None in
  [
    {
      fname = "php";
      doc = "PHP^m_n: m pigeons, n holes (default m = n+1); unsatisfiable iff m > n";
      generate = (fun ps -> let* n = int "n" ps in let* m = int_opt "m" ps in guard (fun () -> php ?m n));
    };
    {
      fname = "tseitin";
      doc = "Tseitin formula on a cycle, grid or complete graph; odd=false gives a satisfiable control";
      generate =
        (fun ps ->
          let* kind = match List.assoc_opt "graph" ps with Some j -> in_context "graph" (D.string j) | None -> error "missing parameter graph" in
          let* size =
            match List.assoc_opt "size" ps with
            | Some (`List [ a; b ]) -> let* a = D.int a in let+ b = D.int b in Two (a, b)
            | Some j -> Result.map (fun k -> One k) (in_context "size" (D.int j))
            | None -> error "missing parameter size"
          in
          let* odd = match List.assoc_opt "odd" ps with Some j -> in_context "odd" (D.bool j) | None -> Ok true in
          guard (fun () -> tseitin ~odd kind size));
    };
    {
      fname = "parity";
      doc = "2·(x1 + … + xn) = 2⌊n/2⌋ + 1 (inequalities): no 0/1 solution, feasible LP relaxation";
      generate = (fun ps -> let* n = int "n" ps in guard (fun () -> parity n));
    };
  ]

let find name = List.find_opt (fun f -> f.fname = name) families

let generate name ps =
  match find name with
  | Some f -> f.generate ps
  | None -> Json.error "unknown family %s (known: %s)" name (String.concat ", " (List.map (fun f -> f.fname) families))

(* the starter suite seeded into a new database *)
let starter () =
  [
    php 1; php 2; php 3; php 4;
    tseitin "cycle" (One 4); tseitin "cycle" (One 6); tseitin "cycle" (One 8);
    tseitin "grid" (Two (2, 3)); tseitin "grid" (Two (3, 3));
    parity 3; parity 5;
    php ~m:3 3; tseitin ~odd:false "cycle" (One 6);
  ]
