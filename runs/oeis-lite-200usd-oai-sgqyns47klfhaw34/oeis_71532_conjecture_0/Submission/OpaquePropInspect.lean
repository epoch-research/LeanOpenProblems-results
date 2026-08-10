import FormalConjectures.Util.ProblemImports
opaque P : Prop
#print P
#check (show P from True.intro)
example : P := by
  change True
  trivial
#print axioms P
#print axioms _example
