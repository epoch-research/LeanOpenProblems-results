import FormalConjectures.Util.ProblemImports

def MyProp2 : ℕ → Prop := fun x => answer(sorry)

theorem MyProp2_proof (x : ℕ) : MyProp2 x := trivial

#print axioms MyProp2
#print axioms MyProp2_proof
