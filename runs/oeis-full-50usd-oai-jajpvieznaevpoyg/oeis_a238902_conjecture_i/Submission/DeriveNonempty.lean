import FormalConjectures.Util.ProblemImports

structure W where
  pr : False
deriving Nonempty

#check W.instNonempty
#print axioms W.instNonempty
