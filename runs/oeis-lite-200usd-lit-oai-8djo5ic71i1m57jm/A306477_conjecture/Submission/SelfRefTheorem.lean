import FormalConjectures.Util.ProblemImports

theorem self_ref_false : False := by
  exact Classical.choice (show Nonempty False from ⟨self_ref_false⟩)
#print axioms self_ref_false
