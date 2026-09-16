import Mathlib

noncomputable def a (n: ℕ) : ℕ := n
noncomputable def sequence_s_int (z : ℤ) : ℕ := a z.toNat

theorem oeis_145062_conjecture_0 :
  ∃ k : ℤ, ∀ n : ℕ, a n = sequence_s_int (n + k) := by
  use 0
  intro n
  have h : (n:ℤ) + 0 = (n:ℤ) := add_zero _
  rw [h]
  have h2 : (n:ℤ).toNat = n := Int.toNat_natCast n
  unfold sequence_s_int
  rw [h2]
