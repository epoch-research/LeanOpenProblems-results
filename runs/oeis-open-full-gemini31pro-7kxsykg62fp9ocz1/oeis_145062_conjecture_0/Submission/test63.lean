import Mathlib

noncomputable def a (n: ℕ) : ℕ := n
noncomputable def sequence_s_int (z : ℤ) : ℕ := if z < 1 then 0 else a (z - 1).toNat

theorem oeis_145062_conjecture_0 :
  ∃ k : ℤ, ∀ n : ℕ, a n = sequence_s_int (n + k) := by
  use 1
  intro n
  unfold sequence_s_int
  split_ifs with h
  · omega
  · congr
    omega
