type 'a t = 'a Seq.t

let map (f : 'a -> 'b) (s : 'a t) : 'b t = Seq.map f s

let return (x : 'a) : 'a t =
  fun () -> Seq.Cons (x, Seq.empty)

let bind (sa : 'a t) (f : 'a -> 'b t) : 'b t =
  Seq.concat_map f sa

(* See the comment over MSeq.delay. *)
let delay (f : unit -> 'a t) : 'a t = 
  fun () -> f () ()

(* This is the main difference with MSeq : in MRand [sum] chooses an argument at random,
 * whereas MSeq keeps all arguments. *)
let sum (li : 'a t list) : 'a t =
  if List.is_empty li then 
    Seq.empty
  else
    let idx = Random.int (List.length li) in
    List.nth li idx

let fail : 'a t = Seq.empty

let one_of (vs : 'a array) : 'a t = 
  if Array.length vs = 0 then 
    Seq.empty
  else
    let idx = Random.int (Array.length vs) in
    fun () -> Seq.Cons (vs.(idx), Seq.empty)

let run (s : 'a t) : 'a Seq.t = s
