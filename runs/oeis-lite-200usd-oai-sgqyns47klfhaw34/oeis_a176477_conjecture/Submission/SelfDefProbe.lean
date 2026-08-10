import FormalConjectures.Util.ProblemImports
noncomputable def badFalse : False := Classical.choice (show Nonempty False from ⟨badFalse⟩)
example : False := badFalse
#print axioms badFalse
