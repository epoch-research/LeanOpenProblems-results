import FormalConjectures.Util.ProblemImports
open scoped Real
noncomputable def a (n : ℕ) : ℝ :=
  let n_r : ℝ := n
  (Real.Gamma (9 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (3 / 2 * n_r + 1)) /
  (Real.Gamma (9 / 2 * n_r + 1) * Real.Gamma (4 * n_r + 1) * Real.Gamma (3 * n_r + 1) * Real.Gamma (n_r + 1))
example : a 2 = 43758 := by norm_num [a, Real.Gamma_nat_eq_factorial]
example : a 1 = 128 := by
  unfold a; norm_num
  rw [(by convert Real.Gamma_nat_add_half 2 using 1 <;> norm_num [Nat.doubleFactorial] : Real.Gamma (5 / 2 : ℝ) = 3 * √Real.pi / 4)]
  rw [(by convert Real.Gamma_nat_add_half 5 using 1 <;> norm_num [Nat.doubleFactorial] : Real.Gamma (11 / 2 : ℝ) = 945 * √Real.pi / 32)]
  field_simp [(Real.sqrt_ne_zero Real.pi_pos.le).2 Real.pi_pos.ne']
  ring
example : a 5 = 2976412336128 := by
  unfold a; norm_num
  -- leave to see goal
