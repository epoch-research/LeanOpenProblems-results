import FormalConjectures.Util.ProblemImports
deriving instance Nonempty for False
example : False := Classical.choice (inferInstance : Nonempty False)
#print axioms DeriveFalse._example_1
