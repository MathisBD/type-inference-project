module Untyped = Untyped.Make (MSeq)
module Infer = Infer.Make (MSeq)
module Solver = Solver.Make (MSeq)
module Constraint = Constraint.Make (MSeq)

let rec indent n str = 
  if n <= 0 then str 
  else String.cat " " (indent (n-1) str)


let () = 
  let term = 
    let open Untyped in 
    let x = Var.fresh "x" in
    let y = Var.fresh "y" in
    Abs (x, 
    Abs (y, 
      Do (MSeq.one_of [| Var x; Var y|] )))
  in 
  let c =   
    let open Constraint in
    let w = Var.fresh "final_type" in
    Exist ( w, None, Conj (
      Infer.has_type Untyped.Var.Map.empty term w,
      Infer.decode w ) )
  in
  let rec solve env c depth =
    let (_, env, nc) = Solver.eval ~log:true env c in
    match nc with 
    (* Victory ! We produced a well-typed term. *)
    | Solver.NRet on_sol -> 
        print_endline (indent depth ">return") ;
        MSeq.return @@ on_sol @@ Decode.decode env
    (* This is what happens when the [untyped] function generates a term that 
     * can't be typed. It's ok, we simply discard this term. *)
    | Solver.NErr _ -> 
        print_endline (indent depth ">error") ;
        MSeq.fail
    (* We reached a Do node : recurse. *)
    | Solver.NDo mc -> 
        print_endline (indent depth ">ndo") ;
        MSeq.bind mc @@ fun c -> solve env c (depth+1)
  in
    solve Unif.Env.empty c 0 
    |> MSeq.run
    |> Seq.map (fun (term, ty) -> 
        PPrint.separate PPrint.hardline [STLCPrinter.print_term term; STLCPrinter.print_ty ty])
    |> List.of_seq
    |> PPrint.(separate (hardline ^^ hardline))
    |> Utils.string_of_doc |> print_endline
  