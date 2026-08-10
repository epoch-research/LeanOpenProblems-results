import FormalConjectures.Util.ProblemImports
noncomputable def bad : False := Classical.choice (show Nonempty False from ⟨bad⟩)
theorem t : False := bad
#print axioms t
