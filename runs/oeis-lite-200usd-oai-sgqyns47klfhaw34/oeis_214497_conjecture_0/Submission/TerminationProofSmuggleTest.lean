import FormalConjectures.Util.ProblemImports

-- Try constant measure; decreasing obligation is impossible.
theorem bad_const_measure (n : ℕ) : False := by
  exact bad_const_measure n
termination_by 0
decreasing_by
  -- cannot prove 0 < 0
  fail_if_success omega
  all_goals simp_wf

-- Try lexicographic-ish but same arg.
theorem bad_same_arg (n : ℕ) : False := by
  exact bad_same_arg n
termination_by n
decreasing_by
  fail_if_success omega
  all_goals simp_wf
