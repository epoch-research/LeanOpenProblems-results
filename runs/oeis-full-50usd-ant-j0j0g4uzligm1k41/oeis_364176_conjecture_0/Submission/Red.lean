import FormalConjectures.Util.ProblemImports
open Real Nat

noncomputable def a (n : ℕ) : ℝ :=
  let n_r : ℝ := n.cast
  ((15 * n).factorial.cast * Real.Gamma (5 * n_r / 2 + 1) * (2 * n).factorial.cast) /
  (Real.Gamma (15 * n_r / 2 + 1) * (6 * n).factorial.cast * (5 * n).factorial.cast * n.factorial.cast)

theorem a_even (m : ℕ) :
    a (2*m) = ((30*m).factorial * (5*m).factorial * (4*m).factorial : ℝ) /
      ((15*m).factorial * (12*m).factorial * (10*m).factorial * (2*m).factorial) := by
  unfold a
  simp only
  have h5 : (5 : ℝ) * ((2*m : ℕ) : ℝ) / 2 + 1 = ((5*m : ℕ) : ℝ) + 1 := by push_cast; ring
  have h15 : (15 : ℝ) * ((2*m : ℕ) : ℝ) / 2 + 1 = ((15*m : ℕ) : ℝ) + 1 := by push_cast; ring
  rw [h5, h15, Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial]
  norm_num
  congr 2 <;> push_cast <;> ring_nf
