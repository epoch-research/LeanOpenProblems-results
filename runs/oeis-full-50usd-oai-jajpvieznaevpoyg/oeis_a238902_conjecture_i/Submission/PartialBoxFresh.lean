import FormalConjectures.Util.ProblemImports

structure Box (P : Prop) where
  pf : P

partial def mkBox (P : Prop) : Box P := mkBox P

example (P : Prop) : P := (mkBox P).pf

#print axioms mkBox
#print axioms PartialBoxFresh._example_1
