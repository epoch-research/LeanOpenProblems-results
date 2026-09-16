import Submission.Spec
open Nat

theorem T : ¬ (type_of% @A357674_conjecture_1) :=
  fun h => (by decide : ¬ (A357674 3 ≡ A357674 1 [MOD 3^5])) (h 3 (by decide) (by decide))
