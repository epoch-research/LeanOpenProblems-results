import FormalConjectures.Util.ProblemImports
open BigOperators Int Real
noncomputable def a (n : ℕ) : ℤ :=
  - Finset.sum (Finset.range n) fun k : ℕ =>
      let k_idx : ℕ := k + 1
      let base_real : ℝ := (3 : ℝ) / 2
      let exponent_int : ℤ := floor (base_real ^ k_idx)
      (-1 : ℤ) ^ exponent_int.toNat

example : a 0 = 0 := by native_decide
example : a 1 = 1 := by native_decide
example : a 2 = 0 := by native_decide
example : a 8 = 6 := by native_decide

example (n : ℕ) : a n ≤ n := by
  unfold a
  -- likely easy? sum of ±1 has abs ≤ n, but try automation
  try omega
  try simp
