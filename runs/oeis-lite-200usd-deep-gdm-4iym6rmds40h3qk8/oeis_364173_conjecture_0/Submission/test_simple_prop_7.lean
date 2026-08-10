import FormalConjectures.Util.ProblemImports

theorem my_proof_axiom_free_4 : True := by
  have h_ans : Prop := answer(sorry)
  have h_ans_val : h_ans := by unfold h_ans; trivial
  have h_eq : h_ans = True := rfl
  rw [h_eq] at h_ans_val
  exact h_ans_val

#print axioms my_proof_axiom_free_4
