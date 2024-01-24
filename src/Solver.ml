(*
   As explained in the README.md ("Abstracting over an effect"),
   this module as well as other modules is parametrized over
   an arbitrary effect [T : Functor].
*)

module Make (T : Utils.Functor) = struct
  module Constraint = Constraint.Make(T)
  module SatConstraint = SatConstraint.Make(T)
  module ConstraintSimplifier = ConstraintSimplifier.Make(T)
  module ConstraintPrinter = ConstraintPrinter.Make(T)

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
    let get_log () =
      logs |> Queue.to_seq |> List.of_seq
    in
    add_to_log, get_log

  (** See [../README.md] ("High-level description") or [Solver.mli]
      for a description of normal constraints and
      our expectations regarding the [eval] function. *)
  type ('a, 'e) normal_constraint =
    | NRet of 'a Constraint.on_sol
    | NErr of 'e
    | NDo of ('a, 'e) Constraint.t T.t

  let eval (type a e) ~log (env : env) (c0 : (a, e) Constraint.t)
    : log * env * (a, e) normal_constraint
  =
    let add_to_log, get_log =
      if log then make_logger c0
      else ignore, (fun _ -> [])
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
    Utils.not_yet "Solver.eval" (env, c0, add_to_log, get_log)

end
