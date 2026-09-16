import Submission.Spec
open Nat

lemma lemma_G : goldbach_binary_conjecture := by
  intro n ⟨h_even, h_gt⟩
  have h_gt_2 : n > 2 := h_gt
  -- Is there any property?
  sorry
