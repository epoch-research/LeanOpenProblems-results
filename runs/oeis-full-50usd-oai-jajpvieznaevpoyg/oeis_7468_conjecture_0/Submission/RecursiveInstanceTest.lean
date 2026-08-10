import FormalConjectures.Util.ProblemImports

noncomputable instance badNonemptyProp (P : Prop) : Nonempty P := inferInstance

example : False := Classical.choice (show Nonempty False from inferInstance)
#print axioms badNonemptyProp
#print axioms _example
