import FormalConjectures.Util.ProblemImports

instance instInh (α : Sort u) : Inhabited α where
  default := (instInh α).default
#print axioms instInh
example : False := (instInh False).default
#print axioms RecursiveInstanceExp._example_1
