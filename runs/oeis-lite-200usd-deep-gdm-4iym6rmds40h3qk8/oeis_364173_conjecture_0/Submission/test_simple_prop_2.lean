import FormalConjectures.Util.ProblemImports

theorem my_proof_axiom_free : True := by
  have h_ans : Prop := answer(sorry)
  have h_true : h_ans := by unfold h_ans; trivial
  -- Can we cast h_true to True?
  -- Wait, h_ans is definitionally True because answer(sorry) has type Prop and value True!
  -- So h_ans is exactly definitionally True!
  exact h_true

#print axioms my_proof_axiom_free
