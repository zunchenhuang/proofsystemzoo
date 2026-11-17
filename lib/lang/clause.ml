type t = int array

let cmp_lit (a : int) (b : int) =
  let c = Int.compare (abs a) (abs b) in
  if c <> 0 then c else Int.compare a b

let of_list lits =
  if List.mem 0 lits then invalid_arg "Clause.of_list: 0 is not a literal";
  Array.of_list (List.sort_uniq cmp_lit lits)

let of_list_strict lits =
  if List.mem 0 lits then Error "0 is not a literal"
  else
    let c = List.sort_uniq cmp_lit lits in
    if List.compare_lengths c lits <> 0 then Error "duplicate literal" else Ok (Array.of_list c)

let empty = [||]
let lits = Array.to_list
let width = Array.length
let is_empty c = Array.length c = 0
let mem (l : int) c = Array.exists (fun x -> x = l) c

let is_tautology c =
  let n = Array.length c in
  let rec go i = i + 1 < n && (c.(i) = - c.(i + 1) || go (i + 1)) in
  go 0

let max_var c = if Array.length c = 0 then 0 else abs c.(Array.length c - 1)

(* linear merge of two sorted literal arrays, skipping [skip_a] in [a] and [skip_b] in [b] *)
let resolve a b v =
  let na = Array.length a and nb = Array.length b in
  let out = Array.make (na + nb) 0 in
  let k = ref 0 and i = ref 0 and j = ref 0 in
  let emit l = if !k = 0 || out.(!k - 1) <> l then (out.(!k) <- l; incr k) in
  while !i < na || !j < nb do
    if !i < na && a.(!i) = v then incr i
    else if !j < nb && b.(!j) = - v then incr j
    else if !j >= nb || (!i < na && cmp_lit a.(!i) b.(!j) <= 0) then (emit a.(!i); incr i)
    else (emit b.(!j); incr j)
  done;
  Array.sub out 0 !k

let subset a b =
  let na = Array.length a and nb = Array.length b in
  let rec go i j =
    if i = na then true
    else if j = nb || na - i > nb - j then false
    else
      let c = cmp_lit a.(i) b.(j) in
      if c = 0 then go (i + 1) (j + 1) else if c > 0 then go i (j + 1) else false
  in
  go 0 0

let compare (a : t) (b : t) =
  let na = Array.length a and nb = Array.length b in
  if na <> nb then Int.compare na nb
  else
    let rec go i = if i = na then 0 else let c = Int.compare a.(i) b.(i) in if c <> 0 then c else go (i + 1) in
    go 0

let equal a b = compare a b = 0
let hash (c : t) = Array.fold_left (fun h l -> (h * 1_000_003) + l) (Array.length c) c land max_int

let to_string c =
  if Array.length c = 0 then "⊥"
  else
    String.concat " ∨ " (List.map (fun l -> if l > 0 then Printf.sprintf "x%d" l else Printf.sprintf "¬x%d" (-l)) (lits c))

let codec : t Json.codec =
  Json.codec (fun c -> Json.E.ints (lits c)) (fun j -> Result.bind (Json.D.list Json.D.int j) of_list_strict)

module Tbl = Hashtbl.Make (struct
  type nonrec t = t
  let equal = equal
  let hash = hash
end)
