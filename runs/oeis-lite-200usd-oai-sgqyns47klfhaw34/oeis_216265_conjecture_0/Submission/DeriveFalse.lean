import FormalConjectures.Util.ProblemImports

deriving instance Nonempty for False

theorem testFalse4 : False := Classical.choice (inferInstance : Nonempty False)
#print axioms testFalse4
