module Make (M : Utils.MonadPlus) : sig
  module Untyped := Untyped.Make(M)
  module Constraint := Constraint.Make(M)
  module Infer := Infer.Make(M)

  val typed : depth:int -> STLC.term M.t
end
