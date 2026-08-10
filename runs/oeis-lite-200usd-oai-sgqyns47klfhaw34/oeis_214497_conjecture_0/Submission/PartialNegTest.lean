import FormalConjectures.Util.ProblemImports

partial def allNeg (P : Prop) : ¬ P := fun h => allNeg P h
partial def allImpFalse (P : Prop) : P → False := fun h => allImpFalse P h
partial def targetNeg : ¬ False := fun h => targetNeg h

#print axioms allNeg
#print axioms allImpFalse
#print axioms targetNeg
