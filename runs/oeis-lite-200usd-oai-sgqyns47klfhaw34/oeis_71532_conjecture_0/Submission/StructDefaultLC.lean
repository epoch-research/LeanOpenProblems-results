import FormalConjectures.Util.ProblemImports
axiom P : Prop
structure S where
  p : P := lcProof
#print axioms S.mk
#check S.mk
example : P := ({} : S).p
#print axioms _example
