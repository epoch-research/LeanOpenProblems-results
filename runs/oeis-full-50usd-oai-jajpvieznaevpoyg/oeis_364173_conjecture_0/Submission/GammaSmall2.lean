import FormalConjectures.Util.ProblemImports
open scoped Real Nat
noncomputable def a (n : ℕ) : ℝ :=
  let n_r : ℝ := n
  (Real.Gamma (9 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (3 / 2 * n_r + 1)) /
  (Real.Gamma (9 / 2 * n_r + 1) * Real.Gamma (4 * n_r + 1) * Real.Gamma (3 * n_r + 1) * Real.Gamma (n_r + 1))
example : Real.Gamma (5/2 : ℝ) = (3 : ℝ) * √Real.pi / 4 := by
  convert Real.Gamma_nat_add_half 2 using 1 <;> norm_num [Nat.doubleFactorial]
example : Real.Gamma (11/2 : ℝ) = (945 : ℝ) * √Real.pi / 32 := by
  convert Real.Gamma_nat_add_half 5 using 1 <;> norm_num [Nat.doubleFactorial]
example : a 1 = 128 := by
  rw [a]
  norm_num
  rw [show Real.Gamma (5/2 : ℝ) = (3 : ℝ) * √Real.pi / 4 by
    convert Real.Gamma_nat_add_half 2 using 1 <;> norm_num [Nat.doubleFactorial]]
  rw [show Real.Gamma (11/2 : ℝ) = (945 : ℝ) * √Real.pi / 32 by
    convert Real.Gamma_nat_add_half 5 using 1 <;> norm_num [Nat.doubleFactorial]]
  ring_nf
  field_simp [Real.sqrt_ne_zero_of_pos Real.pi_pos]
  ring
