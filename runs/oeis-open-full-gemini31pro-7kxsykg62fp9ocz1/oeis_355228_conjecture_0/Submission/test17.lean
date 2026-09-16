import Submission.Spec
open Finset Nat Set

def D4_a08 : Finset ℕ := {1, 2, 3, 6}

lemma D4_a08_card : D4_a08.card = 4 := by rfl
lemma D4_a08_sum : D4_a08.sum id = 12 := by rfl

def D4_a : Finset ℕ := {1, 2, 6, 9}
lemma D4_a_card : D4_a.card = 4 := by rfl
lemma D4_a_sum : D4_a.sum id = 18 := by rfl
lemma D4_a_lcm : D4_a.lcm id = 18 := by rfl
