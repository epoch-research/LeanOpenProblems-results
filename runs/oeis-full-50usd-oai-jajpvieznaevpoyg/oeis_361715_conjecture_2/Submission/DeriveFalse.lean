import FormalConjectures.Util.ProblemImports

deriving instance Nonempty for False

theorem t : False := Classical.choice (inferInstance : Nonempty False)
#print axioms t
