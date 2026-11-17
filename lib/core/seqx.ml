(* Lazy enumeration on top of [Stdlib.Seq].

   Searches enumerate multipliers, juntas and products of high degree; doing
   that with lazy sequences means nothing is materialised unless it is used,
   and a search that stops early (a refutation found, a budget exhausted)
   never pays for the rest of the enumeration. *)

(* [a, b) *)
let range a b : int Seq.t = Seq.init (max 0 (b - a)) (fun i -> a + i)

(* The k-element subsets of [xs], as lists in the order of [xs], in
   lexicographic order of positions. *)
let combinations (xs : 'a array) (k : int) : 'a list Seq.t =
  let n = Array.length xs in
  let rec go start k acc =
    if k = 0 then Seq.return (List.rev acc)
    else Seq.flat_map (fun i -> go (i + 1) (k - 1) (xs.(i) :: acc)) (range start (n - k + 1))
  in
  if k < 0 || k > n then Seq.empty else go 0 k []

(* All subsets of size 0 .. k, smallest first. *)
let subsets_upto (xs : 'a array) (k : int) : 'a list Seq.t =
  Seq.flat_map (combinations xs) (range 0 (min k (Array.length xs) + 1))

(* Short-circuiting fold: stops at the first [Error]. *)
let rec fold_result (f : 'acc -> 'a -> ('acc, 'e) result) (acc : 'acc) (s : 'a Seq.t) : ('acc, 'e) result =
  match s () with
  | Seq.Nil -> Ok acc
  | Seq.Cons (x, rest) -> ( match f acc x with Ok acc -> fold_result f acc rest | Error _ as e -> e)

let iter_result (f : 'a -> (unit, 'e) result) (s : 'a Seq.t) : (unit, 'e) result =
  fold_result (fun () x -> f x) () s

(* Map a list through a result-returning function, keeping order (tail-recursive). *)
let map_result (f : 'a -> ('b, 'e) result) (l : 'a list) : ('b list, 'e) result =
  let rec go acc = function
    | [] -> Ok (List.rev acc)
    | x :: r -> ( match f x with Ok y -> go (y :: acc) r | Error _ as e -> e)
  in
  go [] l
