import FormalConjectures.Util.ProblemImports
opaque P : Prop
opaque pProof : P
theorem bad : P := pProof
#print axioms pProof
#print axioms bad
