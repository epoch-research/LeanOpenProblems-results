import FormalConjectures.Util.ProblemImports

def target : Prop := False
variable [h : Fact target]
instance globalTargetFact : Fact target := h

theorem bad : target := Fact.out
#check globalTargetFact
#check bad
#print axioms globalTargetFact
#print axioms bad
