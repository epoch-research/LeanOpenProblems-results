import FormalConjectures.Util.ProblemImports
noncomputable def badSelf : False := Classical.choice (show Nonempty False from ⟨badSelf⟩)
#print axioms badSelf
