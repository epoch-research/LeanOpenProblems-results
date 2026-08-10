import FormalConjectures.Util.ProblemImports

noncomputable def test_val : ℕ := 2 + 2

theorem test_decide : test_val = 4 := by
  decide
