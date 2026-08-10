import FormalConjectures.Util.ProblemImports

open scoped Real

noncomputable def a (n : ℕ) : ℝ :=
  let n_r : ℝ := n
  (Real.Gamma (9 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (3 / 2 * n_r + 1)) /
  (Real.Gamma (9 / 2 * n_r + 1) * Real.Gamma (4 * n_r + 1) * Real.Gamma (3 * n_r + 1) * Real.Gamma (n_r + 1))

example (k : ℕ) :
    a (2*k) = ((Nat.factorial (18*k) * Nat.factorial (4*k) * Nat.factorial (3*k) : ℕ) : ℝ) /
      ((Nat.factorial (9*k) * Nat.factorial (8*k) * Nat.factorial (6*k) * Nat.factorial (2*k) : ℕ) : ℝ) := by
  unfold a
  norm_num [Real.Gamma_nat_eq_factorial]
  ring

