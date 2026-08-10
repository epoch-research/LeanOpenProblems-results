import FormalConjectures.Util.ProblemImports
open Finset Nat Set
example : (3/5 : ℝ) < Real.log 2 := by
  exact lt_trans (by norm_num : (3/5:ℝ) < 0.6931471803) Real.log_two_gt_d9
example : Real.log 4 < (7/5 : ℝ) := by
  rw [show (4:ℝ)=2^2 by norm_num, Real.log_pow]
  linarith [Real.log_two_lt_d9]
example (n:ℕ) (hn:5000≤n) : Real.log (n:ℝ) ≤ 2 * Real.sqrt (n:ℝ) := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num:0<5000) hn)
  have := Real.log_le_rpow_div (x := (n:ℝ)) (ε := (1/2:ℝ)) (by positivity) (by norm_num)
  rw [show (n:ℝ) ^ (1 / 2 : ℝ) = Real.sqrt (n:ℝ) by rw [Real.sqrt_eq_rpow]] at this
  convert this using 1 <;> ring
