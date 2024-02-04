(*
   As explained in the README.md ("Abstracting over an effect"),
   this module as well as other modules is parametrized over
   an arbitrary effect [T : Functor].
*)

module Make (T : Utils.Functor) = struct
  module Constraint = Constraint.Make (T)
  module SatConstraint = SatConstraint.Make (T)
  module ConstraintSimplifier = ConstraintSimplifier.Make (T)
  module ConstraintPrinter = ConstraintPrinter.Make (T)

  type env = Unif.Env.t
  type log = PPrint.document list

  let make_logger c0 =
    let logs = Queue.create () in
    let c0_erased = SatConstraint.erase c0 in
    let add_to_log env =
      let doc =
        c0_erased
        |> ConstraintSimplifier.simplify env
        |> ConstraintPrinter.print_sat_constraint
      in
      Queue.add doc logs
    in
    let get_log () = logs |> Queue.to_seq |> List.of_seq in
    (add_to_log, get_log)

  (** See [../README.md] ("High-level description") or [Solver.mli]
      for a description of normal constraints and
      our expectations regarding the [eval] function. *)
  type ('a, 'e) normal_constraint =
    | NRet of 'a Constraint.on_sol
    | NErr of 'e
    | NDo of ('a, 'e) Constraint.t T.t

  let do_map (c : ('a, 'e) Constraint.t T.t) (f : ('a, 'e) Constraint.t -> ('b, 'f) Constraint.t) 
      : ('b, 'f) Constraint.t =
    Constraint.Do (T.map f c)
  
  let ndo_map (c : ('a, 'e) Constraint.t T.t) (f : ('a, 'e) Constraint.t -> ('b, 'f) Constraint.t) 
      : ('b, 'f) normal_constraint =
    NDo (T.map f c)
  
  (** Map a function on the result of a normal constraint.
      For [NDo] we delay the actual computations 
      i.e. we add a [Map fret] constraint inside the functor T.
  *)
  let map_nret (fret : 'a -> 'b) (nc : ('a, 'e) normal_constraint) : 
      ('b, 'e) normal_constraint =
    match nc with 
    | NRet on_sol -> NRet (fun sol -> fret (on_sol sol))
    | NErr err -> NErr err
    | NDo c -> ndo_map c @@ fun cinner -> Constraint.Map (cinner, fret)

  (** Map a function on the error of a normal constraint.
      For [NDo] we delay the actual computations 
      i.e. we add a [MapErr ferr] constraint inside the functor T.
  *)
  let map_nerr (ferr : 'e -> 'f) (nc : ('a, 'e) normal_constraint) : 
      ('a, 'f) normal_constraint =
    match nc with 
    | NRet on_sol -> NRet on_sol
    | NErr err -> NErr (ferr err)
    | NDo c -> ndo_map c @@ fun cinner -> Constraint.MapErr (cinner, ferr)

  (** Take the conjunction of the results of two normal constraints.
      
      If at least one of the inputs is [NErr], 
      return [NErr] (choosing arbitrarily the error if both inputs are [NErr]).
      
      If at least one of the inputs is [NDo], 
      return an [NDo] that delays the computation. 
  *)
  let conj (nc : ('a, 'e) normal_constraint) (nc' : ('b, 'e) normal_constraint) :
      ('a * 'b, 'e) normal_constraint =
    match (nc, nc') with 
    (* TODO : for [NDo _, Nerr e], should we instead return [NDo Conj (_, Err e)] ? *)
    | NErr err, _ | _, NErr err -> NErr err
    | NRet on_sol, NRet on_sol' -> NRet (fun sol -> (on_sol sol, on_sol' sol))
    | NDo c, NDo c' -> 
        ndo_map c @@ fun cinner -> 
        do_map c' @@ fun cinner' -> 
        Constraint.Conj (cinner, cinner')
    | NDo c, NRet on_sol' -> 
        ndo_map c @@ fun cinner -> 
        Constraint.Conj (cinner, Constraint.Ret on_sol')
    | NRet on_sol, NDo c' -> 
        ndo_map c' @@ fun cinner' -> 
        Constraint.Conj (Constraint.Ret on_sol, cinner')
            
  let rec eval_aux : type a e. (env -> unit) -> env -> (a, e) Constraint.t -> 
      env * (a, e) normal_constraint =
    fun add_to_log env c ->
    match c with
    | Ret on_sol -> 
        (env, NRet on_sol)
    | Err e -> 
        (env, NErr e)
    | Map (c, fret) -> 
        let (env', nc) = eval_aux add_to_log env c in
        (env', map_nret fret nc)
    | MapErr (c, ferr) ->
        let (env', nc) = eval_aux add_to_log env c in
        (env', map_nerr ferr nc)
    | Conj (c, c') ->
        let (env', nc) = eval_aux add_to_log env c in
        let (env'', nc') = eval_aux add_to_log env' c' in
        (env'', conj nc nc')
    | Eq (w1, w2) ->
        begin match Unif.unify env w1 w2 with 
        | Ok env' -> add_to_log env' ; (env', NRet (fun _ -> ()))
        | Error (Cycle w) -> (env, NErr (Constraint.Cycle w))
        | Error (Clash (w1, w2)) -> 
            Printf.ksprintf failwith 
              "ERROR >>> Clash (%s/%d, %s/%d)\n" w1.name w1.stamp w2.name w2.stamp
            (*(env, NErr (Constraint.Clash (w1, w2)))*)
        end
    | Exist (w, struc, c) -> 
        let env' = Unif.Env.add w struc env in
        add_to_log env' ;
        eval_aux add_to_log env' c
    | Decode w ->
        (env, NRet (fun sol -> sol w))
    | Do c -> 
        (env, NDo c)

  let eval (type a e) ~log (env0 : env) (c0 : (a, e) Constraint.t) :
      log * env * (a, e) normal_constraint =
    let add_to_log, get_log =
      if log then make_logger c0 else (ignore, fun _ -> [])
    in
    (* We recommend calling the function [add_to_log] above
       whenever you get an updated environment. Then call
       [get_log] at the end to get a list of log message.

       $ dune exec -- minihell --log-solver foo.test

       will show a log that will let you see the evolution
       of your input constraint (after simplification) as
       the solver progresses, which is useful for debugging.

       (You can also tweak this code temporarily to print stuff on
       stderr right away if you need dirtier ways to debug.)
    *)
    let (env, nc) = eval_aux add_to_log env0 c0 in
    (get_log(), env, nc)


end
