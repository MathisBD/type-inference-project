module Untyped = Untyped.Make (MSeq)
module Infer = Infer.Make (MSeq)
module Solver = Solver.Make (MSeq)
module Constraint = Constraint.Make (MSeq)

let rec indent n str = 
  if n <= 0 then str 
  else String.cat " " (indent (n-1) str)

let print_env env = 
  let print_var name stamp =
    let v = Constraint.Var.make name stamp in
    try 
      let r = Unif.Env.repr v env in
      match r.structure with 
      | None ->
          Printf.printf "%s ---> %s\n" 
            (Utils.string_of_doc @@ Constraint.Var.print v)
            (Utils.string_of_doc @@ Constraint.Var.print r.var)
      | Some s ->      
          Printf.printf "%s ---> %s (%s)\n" 
            (Utils.string_of_doc @@ Constraint.Var.print v)
            (Utils.string_of_doc @@ Constraint.Var.print r.var)
            (Utils.string_of_doc @@ Structure.print Constraint.Var.print s)
    with Not_found -> ()
  in
  print_var "final_type" 0 ;
  print_var "x" 0 ;
  print_var "y" 0 ;
  print_var "wt" 0 ;
  print_var "wt" 1

let () = 
  let term = 
    let open Untyped in 
    let x = Var.fresh "x" in
    let y = Var.fresh "y" in
    Abs (x, 
    Abs (y, 
      Do (MSeq.one_of [| Var x; Var y |] )))
  in 
  let c =   
    let open Constraint in
    let w = Var.fresh "final_type" in
    Exist ( w, None, Conj (
      Infer.has_type Untyped.Var.Map.empty term w,
      Infer.decode w ) )
  in
  let rec solve table env c depth =
    let (_, env, nc) = Solver.eval ~log:false env c in
    match nc with 
    (* Victory ! We produced a well-typed term. *)
    | Solver.NRet on_sol -> 
        print_endline (indent depth ">return") ;
        MSeq.return @@ on_sol @@ Decode.decode table env
    (* This is what happens when the [untyped] function generates a term that 
     * can't be typed. It's ok, we simply discard this term. *)
    | Solver.NErr _ -> 
        print_endline (indent depth ">error") ;
        MSeq.fail
    (* We reached a Do node : recurse. *)
    | Solver.NDo mc -> 
        print_endline (indent depth ">ndo") ;
        MSeq.bind mc @@ fun c -> solve (Hashtbl.copy table) env c (depth+1)
  in
    solve (Hashtbl.create 42) Unif.Env.empty c 0 
    |> MSeq.run
    |> Seq.map (fun (term, ty) -> 
        PPrint.separate PPrint.hardline [STLCPrinter.print_term term; STLCPrinter.print_ty ty])
    |> List.of_seq
    |> PPrint.(separate (hardline ^^ hardline))
    |> Utils.string_of_doc |> print_endline
  