import Submission.Spec
open Nat

lemma R_true : ∃ n : ℕ, (∃ m, n = m * m) ∧ is_A100570 n := by
  use 0
  constructor
  · exact ⟨0, rfl⟩
  · exact rfl

#print axioms R_true
