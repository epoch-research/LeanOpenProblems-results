import FormalConjectures.Util.ProblemImports
#check lcAny
#print lcAny
#print axioms lcAny
#check lcUnreachable
#print lcUnreachable
#print axioms lcUnreachable
-- try safe use in examples
example : False := by
  exact (lcUnreachable : False)
example : False := by
  exact (lcAny : False)
