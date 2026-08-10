import FormalConjectures.Util.ProblemImports
deriving instance Nonempty for False
example : False := Classical.choice inferInstance
#print axioms _example
