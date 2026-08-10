import FormalConjectures.Util.ProblemImports

structure Bad where
  pf : False
  deriving Nonempty

theorem testFalse3 : False := (Classical.choice (inferInstance : Nonempty Bad)).pf
#print axioms testFalse3
