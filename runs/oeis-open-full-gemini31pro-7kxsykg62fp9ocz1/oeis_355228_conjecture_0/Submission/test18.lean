import Submission.Spec
open Finset Nat Set

def D6 : Finset ℕ := {1, 2, 3, 4, 6, 8}

lemma D6_card : D6.card = 6 := by rfl
lemma D6_sum : D6.sum id = 24 := by rfl
lemma D6_lcm : D6.lcm id = 24 := by rfl
