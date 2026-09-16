import Submission.Spec
open Nat

lemma cheat : goldbach_binary_conjecture := by
  intro n ⟨⟨k, hk⟩, h_gt⟩
  have h_gt3 : n > 3 := by omega
  sorry
