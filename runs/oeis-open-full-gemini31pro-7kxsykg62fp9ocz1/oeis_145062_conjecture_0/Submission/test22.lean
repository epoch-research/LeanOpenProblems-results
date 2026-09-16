import Mathlib

axiom sequence_s_int : ℤ → ℕ

theorem H_disproof : ¬ (∃ k : ℤ, ∀ n : ℕ, sequence_s_int (n + k) = sequence_s_int n) := sorry
