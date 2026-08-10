import FormalConjectures.Util.ProblemImports

#check not_flagged_no_answer_sorry
#check not_flagged_no_arguments
#check not_flagged_non_prop_answer
#print axioms not_flagged_no_arguments
#print axioms not_flagged_non_prop_answer

example : answer(sorry) := by trivial
#print axioms AnswerSafeProbe._example_1

-- can imported theorem imply False?
example : False := by
  have h := not_flagged_non_prop_answer True.intro 0
  -- h : answer(sorry) = 2 ↔ 1+1=2 maybe lhs is True=2? check
  norm_num at h
