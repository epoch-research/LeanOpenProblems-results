import FormalConjectures.Util.ProblemImports
set_option pp.all true
example : True := by
  have h4 := iteratedLog_four
  norm_num at h4
  trace_state
  trivial

example : False := by
  have h4 := iteratedLog_four
  norm_num at h4
  -- if h4 became False contradiction would close?
  assumption
