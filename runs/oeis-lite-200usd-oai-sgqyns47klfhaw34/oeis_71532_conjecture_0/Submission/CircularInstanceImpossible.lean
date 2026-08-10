import FormalConjectures.Util.ProblemImports
class Bad : Prop where h : False
instance instBad : Bad where
  h := by
    exact Bad.h
example : False := Bad.h
#print axioms instBad
#print axioms _example
