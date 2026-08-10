import FormalConjectures.Util.ProblemImports
mutual
noncomputable def bad : False := Classical.choice instBad
noncomputable def instBad : Nonempty False := ⟨bad⟩
end
#print axioms bad
