import FormalConjectures.Util.ProblemImports

def my_ans (P : Prop) : Prop := answer(sorry)

theorem my_proof (P : Prop) : my_ans P := by
  unfold my_ans
  trivial

#print axioms my_proof
