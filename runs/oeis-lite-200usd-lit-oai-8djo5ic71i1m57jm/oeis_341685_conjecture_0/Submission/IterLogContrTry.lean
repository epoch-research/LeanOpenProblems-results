import FormalConjectures.Util.ProblemImports
#check iteratedLog_two
#check iteratedLog_four
#print axioms iteratedLog_four
example : False := by
  have h4 := iteratedLog_four
  -- mathematically Real.log 4 <= 1? no, so iteratedLog_four=2 may be true depending definition.
  guard_target = False
  fail_if_success norm_num at h4
  sorry
