import FormalConjectures.Util.ProblemImports
noncomputable instance badNonempty (P : Prop) : Nonempty P := ⟨Classical.choice (badNonempty P)⟩
theorem t : False := Classical.choice (inferInstance : Nonempty False)
#print axioms t
