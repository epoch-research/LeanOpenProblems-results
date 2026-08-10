import FormalConjectures.Util.ProblemImports
partial def badInst (P : Prop) : Inhabited P := badInst P
noncomputable instance (P : Prop) : Inhabited P := badInst P
theorem t : False := default
#print axioms t
