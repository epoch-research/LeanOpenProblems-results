import Mathlib

noncomputable def a (n: ℕ) : ℕ := n
noncomputable def sequence_s_int (z : ℤ) : ℕ := 0

theorem foo : ¬ (∃ k : ℤ, ∀ n : ℕ, a n = sequence_s_int (n + k)) := by
  intro h
  rcases h with ⟨k, hk⟩
  have h0 := hk 1
  omega
