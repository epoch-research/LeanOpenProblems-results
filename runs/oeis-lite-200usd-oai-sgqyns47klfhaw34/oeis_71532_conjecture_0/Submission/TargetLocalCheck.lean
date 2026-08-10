import FormalConjectures.Util.ProblemImports
open BigOperators Int Real
noncomputable def a (n : ℕ) : ℤ :=
  - Finset.sum (Finset.range n) fun k : ℕ =>
      let k_idx : ℕ := k + 1
      let base_real : ℝ := (3 : ℝ) / 2
      let exponent_int : ℤ := floor (base_real ^ k_idx)
      (-1 : ℤ) ^ exponent_int.toNat

#check Int.cast_nonneg
#check Real.sqrt_nonneg
#check Real.sqrt_lt
#check Real.lt_sqrt
#check sq_lt_sq
#check Int.cast_lt
#check Int.cast_le
example : (a 0 : ℝ) = 0 := by norm_num [a]
example : ¬ ((a 0 : ℝ) > sqrt (0 : ℝ)) := by norm_num [a]
-- if original theorem with N=0 would fail, but N can be >0
