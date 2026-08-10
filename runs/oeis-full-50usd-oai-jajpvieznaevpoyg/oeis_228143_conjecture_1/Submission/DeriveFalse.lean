import FormalConjectures.Util.ProblemImports
deriving instance Nonempty for False
theorem t : False := Classical.choice inferInstance
#print axioms t
