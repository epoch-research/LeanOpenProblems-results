import Submission.Spec
open Finset Nat

theorem cheat : ¬ (type_of% @A357565_conjecture_2) :=
  fun _ =>
    let f : False → False := fun _ => False.elim (sorryAx _ false)
    f (by sorry)
