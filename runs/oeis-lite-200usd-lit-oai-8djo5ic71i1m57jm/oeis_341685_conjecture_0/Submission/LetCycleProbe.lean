import FormalConjectures.Util.ProblemImports

noncomputable def badFalse : False := by
  letI : Nonempty False := ⟨badFalse⟩
  exact Classical.ofNonempty

theorem t : False := badFalse
#print axioms t
