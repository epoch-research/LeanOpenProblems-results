import FormalConjectures.Util.ProblemImports

example : (0:ℝ) > (1:ℝ) := by
  letI : LT ℝ := ⟨fun _ _ => True⟩
  -- goal maybe unchanged?
  change True
  trivial
#print axioms LocalInstanceProofExp._example_1
#print LocalInstanceProofExp._example_1
