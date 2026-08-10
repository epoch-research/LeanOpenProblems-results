import FormalConjectures.Util.ProblemImports

class Bad (P : Prop) where
  pf : P := by
    exact Bad.pf (P := P)

instance instBad (P : Prop) : Bad P := {}
#print axioms instBad
example (P : Prop) : P := Bad.pf (P:=P)
#print axioms ClassDefaultSelf._example_1
