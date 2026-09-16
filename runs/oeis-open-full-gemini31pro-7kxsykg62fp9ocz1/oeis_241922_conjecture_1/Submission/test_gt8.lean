import Submission.Spec
open Nat

#check goldbach_binary_conjecture

lemma test_G : goldbach_binary_conjecture := by
  intro n ⟨⟨k, hk⟩, h_gt⟩
  -- can we just exact sorry?
  exact sorry
