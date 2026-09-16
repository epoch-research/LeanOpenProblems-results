import Mathlib

axiom sequence_s_int : ℤ → ℕ

theorem H_disproof : ¬ (∃ k : ℤ, ∀ n : ℕ, 0 = sequence_s_int (n + k)) := by
  intro h
  rcases h with ⟨k, hk⟩
  sorry

#print axioms H_disproof
