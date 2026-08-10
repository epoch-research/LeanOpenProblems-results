import FormalConjectures.Util.ProblemImports

example : False := by
  -- constant sequence likely not lacunary/Fejer; test automation
  fail_if_success have h : HasFejerGaps (fun _ : ℕ => 1) := by simp [HasFejerGaps]
  sorry
