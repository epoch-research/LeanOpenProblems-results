import Submission.Spec
open Nat

lemma lemma_disproof : ¬ (goldbach_binary_conjecture ↔ ¬ ∃ n : ℕ, (∃ m, n = m * m) ∧ is_A100570 n) := by
  -- is there a way to say ¬(A ↔ B) when A is independent and B is False?
  -- No, if A is independent, then ¬(A ↔ False) is equivalent to A, which is also independent!
  sorry
