import Mathlib

noncomputable def a (n: ℕ) : ℕ := n
noncomputable def sequence_s_int (z : ℤ) : ℕ := if z < 0 then 0 else a z.toNat

theorem test (n : ℕ) : a n = sequence_s_int (n + 0) := by rfl
