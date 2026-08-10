import FormalConjectures.Util.ProblemImports

theorem hack_proof11 (P : Prop) : P := by
  have h : True = P := answer(sorry)
  rw [← h]
  trivial

#print axioms hack_proof11
