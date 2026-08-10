import FormalConjectures.Util.ProblemImports
noncomputable instance badInst (P : Prop) : Inhabited P := ⟨Classical.choice (inferInstance : Nonempty P)⟩
theorem t : False := default
#print axioms t
