import Submission.Spec

lemma R_true : ∃ n : ℕ, (∃ m, n = m * m) ∧ is_A100570 n := by
  use 0
  exact ⟨⟨0, rfl⟩, rfl⟩

#print axioms R_true
