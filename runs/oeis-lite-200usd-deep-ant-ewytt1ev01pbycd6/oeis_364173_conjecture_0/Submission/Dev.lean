import FormalConjectures.Util.ProblemImports

open scoped Real

noncomputable def a (n : ℕ) : ℝ :=
  let n_r : ℝ := n
  (Real.Gamma (9 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (3 / 2 * n_r + 1)) /
  (Real.Gamma (9 / 2 * n_r + 1) * Real.Gamma (4 * n_r + 1) * Real.Gamma (3 * n_r + 1) * Real.Gamma (n_r + 1))

/-- Even case: a(2M) as a ratio of factorials. -/
example (M : ℕ) :
    a (2 * M) =
      ((18 * M).factorial * (4 * M).factorial * (3 * M).factorial : ℝ) /
      ((9 * M).factorial * (8 * M).factorial * (6 * M).factorial * (2 * M).factorial : ℝ) := by
  unfold a
  simp only
  have h2M : ((2 * M : ℕ) : ℝ) = 2 * (M : ℝ) := by push_cast; ring
  rw [h2M]
  -- rewrite each Gamma(k+1) = k!
  have e1 : (9 : ℝ) * (2 * M) + 1 = ((18 * M : ℕ) : ℝ) + 1 := by push_cast; ring
  have e2 : (2 : ℝ) * (2 * M) + 1 = ((4 * M : ℕ) : ℝ) + 1 := by push_cast; ring
  have e3 : (3 / 2 : ℝ) * (2 * M) + 1 = ((3 * M : ℕ) : ℝ) + 1 := by push_cast; ring
  have e4 : (9 / 2 : ℝ) * (2 * M) + 1 = ((9 * M : ℕ) : ℝ) + 1 := by push_cast; ring
  have e5 : (4 : ℝ) * (2 * M) + 1 = ((8 * M : ℕ) : ℝ) + 1 := by push_cast; ring
  have e6 : (3 : ℝ) * (2 * M) + 1 = ((6 * M : ℕ) : ℝ) + 1 := by push_cast; ring
  have e7 : (2 * (M:ℝ)) + 1 = ((2 * M : ℕ) : ℝ) + 1 := by push_cast; ring
  rw [e1, e2, e3, e4, e5, e6, e7, Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial,
      Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial,
      Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial]
