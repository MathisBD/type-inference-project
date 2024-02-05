type 'a t = 'a Seq.t

let map (f : 'a -> 'b) (s : 'a t) : 'b t = Seq.map f s

let return (x : 'a) : 'a t = 
  Seq.return x

let bind (sa : 'a t) (f : 'a -> 'b t) : 'b t =
  Seq.concat_map f sa
  
(* This is quite subtle : we are trying to flatten a two-level thunk 
 * (type [unit -> unit -> 'a]) into a one-level thunk (type [unit -> 'a]). 
 * It's easy here to return [f ()] instead of [fun () -> f () ()] :
 * the former would unfreeze the outer thunk immediately, leaving only the inner thunk frozen,
 * whereas the latter takes care to keep both the outer and inner thunks frozen.
 * It's interesting that in this real world example, eta expansion/reduction 
 * *does* change the semantics of the program. *)
let delay (f : unit -> 'a t) : 'a t = 
  fun () -> f () ()

let sum (li : 'a t list) : 'a t = 
  li |> List.to_seq |> Seq.concat

let fail : 'a t = Seq.empty

let one_of (vs : 'a array) : 'a t = Array.to_seq vs

let run (s : 'a t) : 'a Seq.t = s
