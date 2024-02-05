type 'a t = 'a option

let map (f : 'a -> 'b) (s : 'a t) : 'b t = Option.map f s

let return (x : 'a) : 'a t = Some x

let bind (sa : 'a t) (f : 'a -> 'b t) : 'b t = 
  Option.bind sa f

let delay (f : unit -> 'a t) : 'a t = 
  f ()

let rec sum (li : 'a t list) : 'a t = 
  match li with 
  | [] -> None
  | None :: tl -> sum tl
  | Some hd :: _ -> Some hd

let fail : 'a t = None

let one_of (vs : 'a array) : 'a t = 
  if Array.length vs = 0 then 
    None 
  else 
    Some vs.(0)

let run (s : 'a t) : 'a Seq.t = Option.to_seq s
