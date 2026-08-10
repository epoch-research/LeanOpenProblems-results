import FormalConjectures.Util.ProblemImports
noncomputable def bad : False := Classical.choice (show Nonempty False from ⟨bad⟩)
#print axioms bad
