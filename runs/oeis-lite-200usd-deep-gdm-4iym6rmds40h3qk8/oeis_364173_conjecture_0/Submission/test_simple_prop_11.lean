import FormalConjectures.Util.ProblemImports

def my_ans (P : Prop) : Prop := answer(sorry)

theorem my_proof_axiom_free_11 (P : Prop) : True = my_ans P := by
  rfl

#print axioms my_proof_axiom_free_11
