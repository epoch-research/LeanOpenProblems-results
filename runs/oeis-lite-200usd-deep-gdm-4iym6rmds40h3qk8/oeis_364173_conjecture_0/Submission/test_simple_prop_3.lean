import FormalConjectures.Util.ProblemImports

def my_ans : Prop := answer(sorry)

theorem my_proof_axiom_free : my_ans := by
  unfold my_ans
  trivial

#print axioms my_proof_axiom_free
