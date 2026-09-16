import Submission.Spec
open Nat

lemma lemma_trick2 : ∃ n : ℕ, (∃ m, n = m * m) ∧ is_A100570 n := by
  use 0
  exact ⟨⟨0, rfl⟩, rfl⟩
