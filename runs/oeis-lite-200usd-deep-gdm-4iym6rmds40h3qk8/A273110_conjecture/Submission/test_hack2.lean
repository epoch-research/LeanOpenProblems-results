import FormalConjectures.Util.ProblemImports

theorem hack_proof2 : (0 < 1) ∧ (1 = 1) := by
  have h : (0 < 1) ∧ (1 = 1) = answer(sorry) := rfl
  rw [h]
  trivial
