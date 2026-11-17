(* A growable array, for the imperative inner loops of searches. *)

type 'a t = { mutable data : 'a array; mutable len : int; dummy : 'a }

let create ?(capacity = 16) dummy = { data = Array.make (max 1 capacity) dummy; len = 0; dummy }
let length v = v.len

let get v i =
  if i < 0 || i >= v.len then invalid_arg "Vec.get";
  Array.unsafe_get v.data i

let set v i x =
  if i < 0 || i >= v.len then invalid_arg "Vec.set";
  v.data.(i) <- x

let push v x =
  if v.len = Array.length v.data then begin
    let d = Array.make (2 * v.len) v.dummy in
    Array.blit v.data 0 d 0 v.len;
    v.data <- d
  end;
  v.data.(v.len) <- x;
  v.len <- v.len + 1;
  v.len - 1

let truncate v n = if n < v.len then v.len <- max 0 n
let to_array v = Array.sub v.data 0 v.len
let to_list v = Array.to_list (to_array v)
let iteri f v = for i = 0 to v.len - 1 do f i v.data.(i) done
let to_seq v = Seq.map (fun i -> v.data.(i)) (Seqx.range 0 v.len)
