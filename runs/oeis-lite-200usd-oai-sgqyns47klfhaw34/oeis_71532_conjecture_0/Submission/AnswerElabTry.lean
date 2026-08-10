import FormalConjectures.Util.ProblemImports

example : False := by
  fail_if_success exact (show answer(sorry) from True.intro)
  fail_if_success change answer(sorry)
  fail_if_success exact answer(sorry)
  sorry
