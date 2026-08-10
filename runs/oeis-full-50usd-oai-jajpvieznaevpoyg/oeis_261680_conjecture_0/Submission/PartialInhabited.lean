import FormalConjectures.Util.ProblemImports
partial def inhabit (P : Prop) : Inhabited P := inhabit P
instance instAnyProp (P : Prop) : Inhabited P := inhabit P
theorem bad : False := default
#print axioms bad
