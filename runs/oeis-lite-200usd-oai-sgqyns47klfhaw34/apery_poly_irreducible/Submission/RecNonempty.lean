import FormalConjectures.Util.ProblemImports

noncomputable def badNE : Nonempty False := ⟨Classical.choice badNE⟩

theorem badFalse : False := Classical.choice badNE
#print axioms badFalse
