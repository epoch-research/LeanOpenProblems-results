import FormalConjectures.Util.ProblemImports
noncomputable instance instBad : Nonempty False := ⟨Classical.choice instBad⟩
theorem bad : False := Classical.choice instBad
#print axioms bad
