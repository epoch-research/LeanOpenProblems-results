import FormalConjectures.Util.ProblemImports

partial def eqTrue (P : Prop) : P = True := eqTrue P
partial def iffTrue (P : Prop) : P ↔ True := iffTrue P

#print eqTrue
#print iffTrue
#print axioms eqTrue
#print axioms iffTrue

example (P : Prop) : P := by
  have h := eqTrue P
  exact Eq.mpr h.symm True.intro

#print axioms _example
