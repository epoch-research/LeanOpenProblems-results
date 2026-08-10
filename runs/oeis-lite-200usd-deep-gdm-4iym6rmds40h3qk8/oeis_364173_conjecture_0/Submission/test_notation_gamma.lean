import FormalConjectures.Util.ProblemImports

open scoped Real

local notation "Real.Gamma" => (fun _ : ℝ => (1 : ℝ))

noncomputable def a (n : ℕ) : ℝ :=
  let n_r : ℝ := n
  (Real.Gamma (9 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (3 / 2 * n_r + 1)) /
  (Real.Gamma (9 / 2 * n_r + 1) * Real.Gamma (4 * n_r + 1) * Real.Gamma (3 * n_r + 1) * Real.Gamma (n_r + 1))

theorem a_eq_one (n : ℕ) : a n = 1 := by
  unfold a
  dsimp
  norm_num

#print axioms a_eq_one
