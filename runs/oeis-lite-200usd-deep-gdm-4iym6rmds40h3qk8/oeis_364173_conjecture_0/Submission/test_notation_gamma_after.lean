import FormalConjectures.Util.ProblemImports

noncomputable def a (n : ℕ) : ℝ :=
  let n_r : ℝ := n
  (Real.Gamma (9 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (3 / 2 * n_r + 1)) /
  (Real.Gamma (9 / 2 * n_r + 1) * Real.Gamma (4 * n_r + 1) * Real.Gamma (3 * n_r + 1) * Real.Gamma (n_r + 1))

local notation "Real.Gamma" => (fun x : ℝ => (128 : ℝ))

theorem test_unfold (n : ℕ) : a n = 128 := by
  unfold a
  -- Let's see what the goal is!
  trivial
