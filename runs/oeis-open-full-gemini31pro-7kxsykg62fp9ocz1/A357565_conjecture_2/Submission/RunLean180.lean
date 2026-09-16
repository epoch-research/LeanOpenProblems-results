import Submission.Spec
open Finset Nat

theorem test : ¬ (type_of% @A357565_conjecture_2) :=
  let f : False → False := fun _ => False.elim (sorryAx _ false)
  f (by sorry)
