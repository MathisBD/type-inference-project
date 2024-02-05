module Untyped = Untyped.Make (MSeq)
module Infer = Infer.Make (MSeq)
module Solver = Solver.Make (MSeq)
module Constraint = Constraint.Make (MSeq)
module Generator = Generator.Make (MSeq)


module Env = Map.Make (STLC.TeVar)
let rec build_type (env : STLC.ty Env.t) (t : STLC.term) : STLC.ty = 
  match t with 
  | Var v -> 
      Env.find v env
  | Abs (v, tv, t) -> 
      Constr (Arrow (tv, build_type (Env.add v tv env) t))
  | App (t, u) -> 
      let tt = build_type env t in
      let tu = build_type env u in
      begin match tt with 
      | Constr (Arrow (tt1, tt2)) when tt1 = tu -> tt2
      | _ -> failwith "incorrect type"
      end
  | Let (v, tv, t, u) ->
      let tt = build_type env t in 
      if tt = tv then 
        build_type (Env.add v tv env) u
      else 
        failwith "incorrect type"
  | Annot (t, ty) -> 
      let tt = build_type env t in
      if tt = ty then tt
      else failwith "incorrect type"
  | Tuple ts -> 
      Constr (Prod (List.map (build_type env) ts))
  | LetTuple (vts, t, u) -> 
      let (_, tvs) = List.split vts in
      let tt = build_type env t in
      if tt = Constr (Prod tvs) then
        let env' = List.fold_left (fun env (v, tv) -> Env.add v tv env) env vts in 
        build_type env' u
      else 
        failwith "incorrect type"

let () = 
  let depth = 200 in 
  let count = 100 in
  let terms = 
    Generator.typed ~depth
    |> MSeq.run
    |> Seq.take count
    |> List.of_seq
  in 
    List.iter (fun (term, ty) -> assert (ty = build_type Env.empty term)) terms