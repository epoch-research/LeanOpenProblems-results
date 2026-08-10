import FormalConjectures.Util.ProblemImports

#check Real.iteratedLog
#check iteratedLog_two
#check iteratedLog_four
#check Real.iteratedLog_eq_zero_of_le
#check Real.iteratedLog_eq_zero_of_neg

example : False := by
  have h0 := Real.iteratedLog_eq_zero_of_le (x := (1:ℝ)) (by norm_num)
  -- compare with definition maybe
  norm_num at h0
  guard_target = False
  fail_if_success exact (zero_ne_one h0)
  sorry
