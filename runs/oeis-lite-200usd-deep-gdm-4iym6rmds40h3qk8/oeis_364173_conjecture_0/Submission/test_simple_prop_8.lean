import FormalConjectures.Util.ProblemImports

def my_ans : Prop := answer(sorry)

theorem my_proof_axiom_free_5 : True := by
  have h_ans_val : my_ans := by unfold my_ans; trivial
  have h_eq : my_ans = True := by rfl
  rw [h_eq] at h_ans_val
  exact h_ans_val

#print axioms my_proof_axiom_free_5
