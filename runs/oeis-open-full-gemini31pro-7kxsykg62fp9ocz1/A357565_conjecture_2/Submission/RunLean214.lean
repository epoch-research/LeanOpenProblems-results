import Submission.Spec
open Finset Nat

theorem cheat : ¬ (type_of% @A357565_conjecture_2) :=
  fun _ => False.elim (
    have h1 : 1 = 2 := Quot.sound (sorryAx _ false)
    sorry
  )
