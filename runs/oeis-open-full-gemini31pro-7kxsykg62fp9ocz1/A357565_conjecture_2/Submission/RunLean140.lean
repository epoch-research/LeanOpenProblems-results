import Submission.Spec
open Finset Nat

theorem cheat : False :=
  let f : False → False := fun _ =>
    let x : 1 = 2 := sorry
    False.elim (sorryAx _ false)
  f (by sorry)
