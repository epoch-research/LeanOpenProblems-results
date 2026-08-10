import FormalConjectures.Util.ProblemImports

def P : Prop := True
instance instP : Fact P := inferInstance

theorem T : P := Fact.out
#print axioms T
