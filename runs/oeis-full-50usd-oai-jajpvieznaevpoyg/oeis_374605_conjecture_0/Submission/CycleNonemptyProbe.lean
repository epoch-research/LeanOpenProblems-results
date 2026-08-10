import FormalConjectures.Util.ProblemImports
noncomputable def neFalse : Nonempty False := ⟨Classical.choice neFalse⟩
theorem tFalse : False := Classical.choice neFalse
#print axioms tFalse
