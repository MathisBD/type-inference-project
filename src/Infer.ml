(** Infer contains the logic to generate an inference constraint from
    an untyped term, that will elaborate to an explicitly-typed term
    or fail with a type error. *)

(* You have to implement the [has_type] function below,
   which is the constraint-generation function. *)

module Make (T : Utils.Functor) = struct
  module Constraint = Constraint.Make (T)
  open Constraint
  module Untyped = Untyped.Make (T)

  module Env = Untyped.Var.Map
  (** The "environment" of the constraint generator maps each program
      variable to an inference variable representing its (monomorphic)
      type.

      For example, to infer the type of the term [lambda x. t], we
      will eventually call [has_type env t] with an environment
      mapping [x] to a local inference variable representing its type.
  *)

  type env = variable Env.t

  type err = eq_error =
    | Clash of STLC.ty Utils.clash
    | Cycle of Constraint.variable Utils.cycle

  type 'a constraint_ = ('a, err) Constraint.t

  (** [ex] and [ex_eq] allow us to build Exist constraints in a monadic fashion. 
      Usage example :
      {[
        ex_eq "warr" (Arrow (w1, w2)) @@ fun w -> 
        __some_constraint__(w)
      ]}

      This expands to :
      {[
        let w = Var.fresh "warr" in
        Exist(w, Some (Arrow (w1, w2)), __some_constraint__(w))
      ]}

  *)
  let ex name c = 
    let v = Var.fresh name in Exist (v, None, c v)
  let ex_eq name s c = 
    let v = Var.fresh name in Exist (v, Some s, c v)

  let eq v1 v2 = Eq (v1, v2)
  let decode v = MapErr (Decode v, fun e -> Cycle e)

  let assume_pair = function
    | [ v1; v2 ] -> (v1, v2)
    | other ->
        Printf.ksprintf failwith
          "Error: this implementation currently only supports pairs,\n\
          \         not tuples of size %d." (List.length other)

  (** This is a helper function to implement constraint generation for
      the [Annot] construct.
     
      [bind ty k] takes a type [ty], and a constraint [k] parametrized
      over a constraint variable. It creates a constraint context that
      binds a new constraint variable [?w] that must be equal to [ty],
      and places [k ?w] within this context.
      
      For example, if [ty] is the type [?v1 -> (?v2 -> ?v3)] , then
      [bind ty k] could be the constraint
        [∃(?w1 = ?v2 -> ?v3). ∃(?w2 = ?v1 -> ?w1). k ?w2], or equivalently
        [∃?w3 ?w4. ?w3 = ?v1 -> ?w4 ∧ ?w4 = ?v2 -> ?v3 ∧ k ?w3].
  *)
  let rec bind (ty : STLC.ty) (k : Constraint.variable -> ('a, 'e) t) :
      ('a, 'e) t =
    match ty with
    | Constr (Var v) ->
        ex_eq v.name (Var v) @@ fun w ->
        k w
    | Constr (Arrow (ty1, ty2)) ->
        bind ty1 @@ fun w1 ->
        bind ty2 @@ fun w2 ->
        ex_eq "w" (Arrow (w1, w2)) @@ fun w ->
        k w
    | Constr (Prod tys) ->
        let ty1, ty2 = assume_pair tys in
        bind ty1 @@ fun w1 ->
        bind ty2 @@ fun w2 ->
        ex_eq "w" (Prod [ w1; w2 ]) @@ fun w ->
        k w

  (** This function generates a typing constraint from an untyped term:
      [has_type env t w] generates a constraint [C] which contains [w] as
      a free inference variable, such that [C] has a solution if and only
      if [t] is well-typed in [env], and in that case [w] is the type of [t].

      For example, if [t] is the term [lambda x. x], then [has_type env t w]
      generates a constraint equivalent to [∃?v. ?w = (?v -> ?v)].

      Precondition: when calling [has_type env t], [env] must map each
      term variable that is free in [t] to an inference variable.
  *)
  let rec has_type (env : env) (t : Untyped.term) (w : variable) :
      (STLC.term, err) t =
    match t with
    | Untyped.Var x ->
        let+ _ = eq w (Env.find x env)
        in STLC.Var x
    | Untyped.App (t, u) ->
        ex "wu" @@ fun wu ->
        ex_eq "wt" (Arrow (wu, w)) @@ fun wt ->
        let+ t' = has_type env t wt 
        and+ u' = has_type env u wu
        in STLC.App (t', u')
    | Untyped.Abs (x, t) ->
        ex x.name @@ fun wx ->
        ex "wt" @@ fun wt ->
        ex_eq "warr" (Arrow (wx, wt)) @@ fun warr ->
        let+ t' = has_type (Env.add x wx env) t wt
        and+ _ = eq w warr
        and+ tx = decode wx 
        in STLC.Abs (x, tx, t')
    | Untyped.Let (x, t, u) ->
        ex x.name @@ fun wx ->
        let+ t' = has_type env t wx
        and+ u' = has_type (Env.add x wx env) u w
        and+ tx = decode wx 
        in STLC.Let (x, tx, t', u')
    | Untyped.Annot (t, ty) ->
        bind ty @@ fun v ->
        let+ t' = has_type env t v 
        and+ _ = eq v w 
        in t'
    | Untyped.Tuple ts ->
        let t1, t2 = assume_pair ts in
        ex "w1" @@ fun w1 ->
        ex "w2" @@ fun w2 ->
        ex_eq "wprod" (Prod [ w1; w2 ]) @@ fun wprod ->
        let+ t1' = has_type env t1 w1
        and+ t2' = has_type env t2 w2
        and+ _ = eq wprod w 
        in STLC.Tuple [ t1'; t2' ]
    | Untyped.LetTuple (xs, t, u) ->
        let x1, x2 = assume_pair xs in
        ex "w1" @@ fun w1 ->
        ex "w2" @@ fun w2 ->
        ex_eq "wprod" (Prod [ w1; w2 ]) @@ fun wprod ->
        let+ t' = has_type env t wprod
        and+ u' = has_type (env |> Env.add x1 w1 |> Env.add x2 w2) u w
        and+ tx1 = decode w1
        and+ tx2 = decode w2
        in STLC.LetTuple ([ (x1, tx1); (x2, tx2) ], t', u')
    | Do p ->
        Do (T.map (fun t -> has_type env t w) p)
end
