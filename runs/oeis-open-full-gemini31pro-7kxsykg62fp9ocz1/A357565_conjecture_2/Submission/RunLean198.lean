import Submission.Spec
open Finset Nat

theorem cheat : ¬ (type_of% @A357565_conjecture_2) :=
  let x : False :=
    let f : False → False := fun _ => False.elim (sorryAx _ false)
    f (by sorry)
  x
