import FormalConjectures.Util.ProblemImports
def P0 : Prop := False
instance instP0 : Nonempty P0 := ⟨Classical.choice instP0⟩
theorem badP0 : P0 := Classical.choice instP0
#print axioms badP0
