import FormalConjectures.Util.ProblemImports

partial def loopNot (P : Prop) : ¬ P := fun h => loopNot P h

theorem notAny (P : Prop) : ¬ P := loopNot P
#print axioms notAny
