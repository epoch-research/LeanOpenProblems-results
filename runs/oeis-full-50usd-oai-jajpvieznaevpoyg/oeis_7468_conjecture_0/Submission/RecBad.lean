import FormalConjectures.Util.ProblemImports

noncomputable def bad (P : Prop) : Nonempty P := bad P
example : False := Classical.choice (bad False)
#print axioms bad
#print axioms _example
