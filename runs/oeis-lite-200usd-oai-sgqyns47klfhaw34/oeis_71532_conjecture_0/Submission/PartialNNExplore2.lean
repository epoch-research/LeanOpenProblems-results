import FormalConjectures.Util.ProblemImports

partial def nn1 (P : Prop) (h : ¬ P) : False := nn1 P h
partial def nn2 (P : Prop) : ¬¬P := fun h => nn2 P h
partial def cont (P : Prop) : (P → Empty) → Empty := fun h => cont P h
partial def imp (P Q : Prop) (h : P) : Q := imp P Q h

example (P : Prop) : P := by
  classical
  exact byContradiction (nn2 P)

#print axioms nn1
#print axioms nn2
#print axioms cont
#print axioms imp
#print axioms _example
