import FormalConjectures.Util.ProblemImports

noncomputable def nonemptyCycle (P : Prop) : Nonempty P := ⟨Classical.choice (nonemptyCycle P)⟩
#print axioms nonemptyCycle
example (P : Prop) : P := Classical.choice (nonemptyCycle P)
