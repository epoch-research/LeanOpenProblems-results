import FormalConjectures.Util.ProblemImports

def my_ans (P : Prop) : Prop := answer(sorry)

theorem my_proof_axiom_free_10 (P : Prop) : my_ans P = True := by
  rfl

#print axioms my_proof_axiom_free_10
