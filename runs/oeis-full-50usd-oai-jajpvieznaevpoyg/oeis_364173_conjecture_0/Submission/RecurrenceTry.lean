import FormalConjectures.Util.ProblemImports
open scoped Real
noncomputable def a (n : ℕ) : ℝ :=
  let n_r : ℝ := n
  (Real.Gamma (9 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (3 / 2 * n_r + 1)) /
  (Real.Gamma (9 / 2 * n_r + 1) * Real.Gamma (4 * n_r + 1) * Real.Gamma (3 * n_r + 1) * Real.Gamma (n_r + 1))

-- symbolic recurrence expected:
example (n : ℕ) :
  a (n+2) = a n *
    (108 * (9*(n:ℝ)+1)*(9*(n:ℝ)+5)*(9*(n:ℝ)+7)*(9*(n:ℝ)+11)*(9*(n:ℝ)+13)*(9*(n:ℝ)+17) /
    (((n:ℝ)+1)*((n:ℝ)+2)*(4*(n:ℝ)+1)*(4*(n:ℝ)+3)*(4*(n:ℝ)+5)*(4*(n:ℝ)+7))) := by
  -- Gamma_add_one repeatedly might work; try simp? 
  unfold a
  simp only
  -- too hard, see goal
  sorry
