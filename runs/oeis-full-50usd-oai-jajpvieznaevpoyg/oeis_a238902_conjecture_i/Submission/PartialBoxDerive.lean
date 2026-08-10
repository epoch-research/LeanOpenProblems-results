import FormalConjectures.Util.ProblemImports

structure Box (P : Prop) where
  pf : P
  deriving Nonempty

#check Box.instNonempty
partial def mkBox (P : Prop) : Box P := mkBox P
example (P : Prop) : P := (mkBox P).pf
#print axioms Box.instNonempty
#print axioms mkBox
