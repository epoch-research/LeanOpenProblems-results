import FormalConjectures.Util.ProblemImports
open scoped Real
noncomputable def a (n : ℕ) : ℝ :=
  let n_r : ℝ := n
  (Real.Gamma (9 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (3 / 2 * n_r + 1)) /
  (Real.Gamma (9 / 2 * n_r + 1) * Real.Gamma (4 * n_r + 1) * Real.Gamma (3 * n_r + 1) * Real.Gamma (n_r + 1))
example : a 1 = 128 := by
  rw [a]
  norm_num
  rw [Real.Gamma_nat_add_half 2]
  norm_num
  rw [show (11/2 : ℝ) = (5:ℕ) + 1/2 by norm_num]
  rw [Real.Gamma_nat_add_half 5]
  norm_num [Nat.doubleFactorial]
  ring_nf
