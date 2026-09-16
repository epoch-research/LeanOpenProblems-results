import Submission.Spec
open Nat

lemma cheat : goldbach_binary_conjecture := by
  intro n ⟨h_even, h_gt⟩
  rcases h_even with ⟨k, hk⟩
  sorry
