import FormalConjectures.Util.ProblemImports
#check Part.get_eq_get
#check dom_of_apply_eq_none
#check Turing.eval_dom_iff
#print axioms Part.get_eq_get
#print axioms Turing.eval_dom_iff

-- try Part equality false? a = none, b = some etc hypotheses should impossible.
example : False := by
  norm_num
