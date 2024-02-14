(* This is a state monad on top of an option monad. 
 * The option ensures we can fail, and the state is the random seed we use. 
 * When we generate a random number (rand_int), we use the input seed,
 * and we update the seed using a pseudo-random generator.
 * To obtain a different result, use a different seed as input. *)
type 'a t = int -> 'a option * int

(* Compute the next state in the pseudo-random number sequence. 
 * Before using the seed, make sure to shift it right by 16 bits : 
 *   [seed lsr 16] 
 * The values were taken from https://rosettacode.org/wiki/Linear_congruential_generator#OCaml *)
let next_seed (seed : int) : int = 
  (214013 * seed + 2531011) land 0x7fffffff

let map (f : 'a -> 'b) (x : 'a t) : 'b t = 
  fun seed -> 
    let (res, seed') = x seed in 
    (Option.map f res, seed')

let return (x : 'a) : 'a t =
  fun seed -> (Some x, seed)

let bind (x : 'a t) (f : 'a -> 'b t) : 'b t =
  fun seed -> 
    match x seed with 
    | (None, _) as res -> res
    | (Some y, seed') -> f y seed'
        
let delay (f : unit -> 'a t) : 'a t = 
  fun seed -> f () seed

(* [fail] is the reason why we need to use an option. *)
let fail : 'a t = 
  fun seed -> (None, seed)

(* Generate a random number in range [0, n-1] and UPDATE THE SEED. *)
let rand_int (n : int) : int t = 
  if n <= 0 then 
    fail 
  else 
    fun seed -> 
      let i = (seed lsr 16) mod n in 
      (Some i, next_seed seed)

(* The implementation of [sum] uses a trick to speed up generation. 
 * If we choose and index that corresponds to a value that evaluates to None, 
 * instead of simply returning None (which would cause the entire computation to be run again
 * with a different seed), we remove the offending value and try again.
 * This results in a huge speedup (orders of magnitude), especially on large terms (depth ~ 40).
 * 
 * depth | NAIVE | TRICK 
 * 25    | 20ms  | 0.8ms
 * 30    | 60ms  | 1.5ms
 * 35    | 200ms | 2.7ms
 * 40    | 800ms | 4.6ms
 * 45    | 3s    | 8.0ms
 * Using this optimization I can generate a term of depth up to ~100 in under a second.
 *)
(*let rec sum (li : 'a t list) : 'a t =
  fun seed -> 
    match rand_int (List.length li) seed with 
    (* The list is empty. *)
    | (None, _) as res -> res
    (* The list is not empty. *)
    | (Some idx, seed) -> 
        (* Here it would be correct to simply return [List.nth li idx seed]. *)
        begin match List.nth li idx seed with 
        (* The index we chose indeed produces an value : we succeeded. *)
        | (Some _, _) as res -> res 
        (* The index we chose produces None : remove it from li and try again. *)
        | (None, seed) -> sum (List.filteri (fun i _ -> i <> idx) li) seed
        end*)

let sum (li : 'a t list) : 'a t =
  fun seed -> 
    match rand_int (List.length li) seed with 
    (* The list is empty. *)
    | (None, _) as res -> res
    (* The list is not empty. *)
    | (Some idx, seed) -> List.nth li idx seed

let one_of (vs : 'a array) : 'a t = 
  vs |> Array.to_list |> List.map return |> sum

let run (s : 'a t) : 'a Seq.t =
  let seq = Seq.forever @@ fun () -> fst @@ s @@ Random.int 1000000 in 
  Seq.concat_map 
    (function None -> Seq.empty | Some x -> Seq.return x) 
    seq

