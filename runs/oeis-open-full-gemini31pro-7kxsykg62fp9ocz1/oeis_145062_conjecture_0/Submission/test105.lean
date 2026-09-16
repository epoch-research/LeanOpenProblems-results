import Mathlib

noncomputable def a (n: ℕ) : ℕ := n
noncomputable def sequence_s_int (z : ℤ) : ℕ := a (z.toNat - 1)

theorem oeis_145062_conjecture_0 :
  ∃ k : ℤ, ∀ n : ℕ, a n = sequence_s_int (n + 1) := by
  use 1
  intro n
  unfold sequence_s_int
  try rfl
