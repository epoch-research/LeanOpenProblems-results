import FormalConjectures.Util.ProblemImports
structure Bad where
  pr : False
  deriving Nonempty
#check (Classical.choice (inferInstance : Nonempty Bad)).pr
example : False := (Classical.choice (inferInstance : Nonempty Bad)).pr
#print axioms Bad.instNonempty
#print axioms (show False from (Classical.choice (inferInstance : Nonempty Bad)).pr)
