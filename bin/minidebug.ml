module Untyped = Untyped.Make (MSeq)
module Infer = Infer.Make (MSeq)
module Solver = Solver.Make (MSeq)
module Constraint = Constraint.Make (MSeq)

let rec indent n str = 
  if n <= 0 then str 
  else String.cat " " (indent (n-1) str)


let () = 
  (*let term = 
    let open Untyped in 
    let x = Var.fresh "x" in
    Abs (x, Do (MSeq.return @@ Var x))
  in 
  let c =   
    let open Constraint in
    let w = Var.fresh "final_type" in
    Exist ( w, None, Infer.has_type Untyped.Var.Map.empty term w )
  in *)
  let c = 
    let open Constraint in 
    let a = Var.fresh "a" in 
    let b = Var.fresh "b" in 
    Exist (a, None, 
    Exist (b, None, 
      Conj ( 
        Eq (a, b),
        Do MSeq.fail ) )
    )
  in
  ignore @@ Solver.eval ~log:true Unif.Env.empty c

  (*let solve env c depth =
    let (_, env, nc) = Solver.eval ~log:true env c in
    match nc with 
    (* Victory ! We produced a well-typed term. *)
    | Solver.NRet on_sol -> 
        print_endline (ident depth ">return") ;
        MSeq.return @@ on_sol @@ Decode.decode env
    (* This is what happens when the [untyped] function generates a term that 
     * can't be typed. It's ok, we simply discard this term. *)
    | Solver.NErr _ -> 
        print_endline (ident depth ">error") ;
        MSeq.fail
    (* We reached a Do node : recurse. *)
    | Solver.NDo _ -> 
        failwith (ident depth ">ndo")
        (*M.bind mc @@ fun c -> solve env c (depth+1)*)
  in
    ignore @@ solve Unif.Env.empty c 0*)
