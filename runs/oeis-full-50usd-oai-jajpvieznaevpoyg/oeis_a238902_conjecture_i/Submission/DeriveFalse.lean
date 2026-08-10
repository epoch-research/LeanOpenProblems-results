import FormalConjectures.Util.ProblemImports
deriving instance Nonempty for False
#check (inferInstance : Nonempty False)
theorem bad : False := Classical.choice inferInstance
#print axioms bad
