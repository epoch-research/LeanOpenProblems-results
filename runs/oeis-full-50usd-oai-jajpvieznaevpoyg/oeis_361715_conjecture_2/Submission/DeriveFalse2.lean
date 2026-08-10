import FormalConjectures.Util.ProblemImports

deriving instance Nonempty for False
-- deriving instance Inhabited for False
example : False := Classical.choice (inferInstance : Nonempty False)
#print axioms «example»
