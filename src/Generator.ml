module Make (M : Utils.MonadPlus) = struct
  module Untyped = Untyped.Make (M)
  module Constraint = Constraint.Make (M)
  module Infer = Infer.Make (M)
  module Solver = Solver.Make (M)

  (* just in case... *)
  module TeVarSet = Untyped.Var.Set
  module TyVarSet = STLC.TyVar.Set

  let new_name = Untyped.Var.namegen [| "x"; "y"; "z"; "u"; "v" |]

  (** Generate an integer in the range min (included) to max (excluded). *)
  (*let gen_int (min : int) (max : int) : int M.t =
    if min >= max then 
      M.fail
    else
      M.one_of @@ Array.init (max - min) (fun i -> min + i)

  (** Split a given quantity of [fuel] in two strictly positive sub-quantities whose sum is [fuel]. *)
  let split_fuel (fuel : int) : (int * int) M.t =
    M.map (fun f -> (f, fuel - f)) (gen_int 1 fuel) *)

  (** Generate an untyped term. The term will be closed (no free variables).
      Parameter [vars] is the set of bound variables we are allowed use.
      Parameter [fuel] is the number of [Do] nodes we can (and have to) use (in total, not per branch). 
  *)
  let rec gen_term ~(fuel: int) (vars : TeVarSet.t) () : Untyped.term =
    let open Untyped in 
    (* No more fuel left. This case really happens : let's say we want to generate a term 
     * with fuel=2, the App case for instance will recursively try to generate terms with fuel=0 and fuel=1,
     * which as expected will fail. *)
    if fuel <= 0 then Do M.fail
    (* Generate a variable. *)
    else if fuel = 1 then
      (* Get a valid variable identifier. *)
      (*let v = M.delay @@ fun () -> M.one_of @@ Array.of_list @@ TeVarSet.to_list vars in
      (* We can't return a [Var] node because [v] is not an identifier but an identifier in the monad 
       * (for instance in MSeq [v] would be a sequence of identifiers).
       * We have to wrap [Var] in a [Do] node. *)
      Do (M.map (fun v' -> Var v') v)*)
      Do (M.return @@ Var (TeVarSet.choose vars))
    else  
      let x = new_name () in
      Abs ( x, gen_term ~fuel:(fuel - 1) (TeVarSet.add x vars) () )
  
      (* Pick a random node that isn't a variable. *)
      (*Do 
        ( M.delay @@ fun () ->
          M.sum 
            [
              (* App. *)
              (*begin 
                M.bind (split_fuel (fuel - 1)) @@ fun (f1, f2) ->
                M.return @@ App (
                  gen_term ~fuel:f1 vars (), 
                  gen_term ~fuel:f2 vars () )
              end;*)
              (* Abs. *)
              begin 
                let x = new_name () in
                M.return @@ Abs (
                  x, 
                  gen_term ~fuel:(fuel - 1) (TeVarSet.add x vars) () )
              end;
              (* Let. *)
              (*begin 
                let x = new_name () in 
                M.bind (split_fuel (fuel - 1)) @@ fun (f1, f2) ->
                M.return @@ Let (
                  x, 
                  gen_term ~fuel:f1 vars (),
                  gen_term ~fuel:f2 (TeVarSet.add x vars) () )
              end;
              (* Tuple. *)
              begin 
                M.bind (split_fuel (fuel - 1)) @@ fun (f1, f2) ->
                M.return @@ Tuple [
                  gen_term ~fuel:f1 vars ();
                  gen_term ~fuel:f2 vars () ]
              end;
              (* LetTuple. *)
              begin
                let x = new_name () in 
                let y = new_name () in 
                M.bind (split_fuel (fuel - 1)) @@ fun (f1, f2) ->
                M.return @@ LetTuple (
                  [x; y],
                  gen_term ~fuel:f1 vars (),
                  gen_term ~fuel:f2 (vars |> TeVarSet.add x |> TeVarSet.add y) () )
              end;*)
            ] )*)

  let rec indent n str = 
    if n <= 0 then str 
    else String.cat " " (indent (n-1) str)

  let typed ~depth =
    (* Build an untyped term lazily (i.e. most computations are frozen at Do nodes). *)
    let term = gen_term ~fuel:depth TeVarSet.empty () in
    (* Build a constraint, again lazily (type inference stops at Do nodes 
     * provided M is lazy). *)
    let c0 =
      let open Constraint in
      let w = Var.fresh "final_type" in
      Exist ( w, None, Conj (
        Infer.has_type Untyped.Var.Map.empty term w, 
        Infer.decode w ) )
    in
    (* Generate terms by applying the constraint solver recursively. *)
    let rec solve env c depth =
      let (_, env, nc) = Solver.eval ~log:true env c in
      (* Print the log. *)
      (*log 
        |> PPrint.(separate (hardline))
        |> Utils.string_of_doc 
        |> print_endline ;*)
      match nc with 
      (* Victory ! We produced a well-typed term. *)
      | Solver.NRet on_sol -> 
          print_endline (indent depth ">return") ;
          M.return @@ on_sol @@ Decode.decode env
      (* This is what happens when the [untyped] function generates a term that 
       * can't be typed. It's ok, we simply discard this term. *)
      | Solver.NErr _ -> 
          print_endline (indent depth ">error") ;
          M.fail
      (* We reached a Do node : recurse. *)
      | Solver.NDo mc -> 
          print_endline (indent depth ">ndo") ;
          M.bind mc @@ fun c -> solve env c (depth+1)
    in
      solve Unif.Env.empty c0 0
end
