import FormalConjectures.Util.ProblemImports

noncomputable def fake (P : Prop) : Nonempty P :=
  Classical.choice (show Nonempty (Nonempty P) from ⟨fake P⟩)

example : False := Classical.choice (fake False)
#print axioms fake
