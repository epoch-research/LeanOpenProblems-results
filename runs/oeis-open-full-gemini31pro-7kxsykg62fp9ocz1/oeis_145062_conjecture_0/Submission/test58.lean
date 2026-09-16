import Mathlib

noncomputable def a (n: ℕ) : ℕ := n
noncomputable def sequence_s_int (z : ℤ) : ℕ := a z.toNat

theorem oeis_145062_conjecture_0 :
  ∃ k : ℤ, ∀ n : ℕ, a n = sequence_s_int (n + k) := by
  use 0
  intro n
  rfl
