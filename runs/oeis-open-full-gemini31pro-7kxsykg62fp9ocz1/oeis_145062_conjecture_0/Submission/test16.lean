import Mathlib
axiom sequence_s_int : ℤ → ℕ
theorem H_disproof : ¬ (∃ k : ℤ, ∀ n : ℕ, 0 = sequence_s_int (n + k)) := sorry
#print axioms H_disproof
