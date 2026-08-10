import FormalConjectures.Util.ProblemImports

#check Real.iteratedLog
#check Real.iteratedLog_eq_zero_of_le
#check Real.iteratedLog_eq_zero_of_neg
#check iteratedLog_two
#check iteratedLog_four

example : False := by
  have h0 := Real.iteratedLog_eq_zero_of_le (x := 1) (by norm_num)
  have h2 := iteratedLog_two
  -- no contradiction expected
  norm_num at h0 h2

example : False := by
  have h4 := iteratedLog_four
  have hle := Real.iteratedLog_eq_zero_of_le (x := 4) (by norm_num)
  norm_num at h4 hle
