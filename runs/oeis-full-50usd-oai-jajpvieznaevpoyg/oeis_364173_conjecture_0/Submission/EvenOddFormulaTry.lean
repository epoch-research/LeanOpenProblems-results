import FormalConjectures.Util.ProblemImports
open scoped Real
noncomputable def a (n : ℕ) : ℝ :=
  let n_r : ℝ := n
  (Real.Gamma (9 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (3 / 2 * n_r + 1)) /
  (Real.Gamma (9 / 2 * n_r + 1) * Real.Gamma (4 * n_r + 1) * Real.Gamma (3 * n_r + 1) * Real.Gamma (n_r + 1))

example (k : ℕ) : a (2*k) =
    (( (18*k).factorial * (4*k).factorial * (3*k).factorial : ℕ) : ℝ) /
    (((9*k).factorial * (8*k).factorial * (6*k).factorial * (2*k).factorial : ℕ) : ℝ) := by
  unfold a
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  -- expected all Gamma_nat_eq_factorial
  norm_num [Real.Gamma_nat_eq_factorial]
