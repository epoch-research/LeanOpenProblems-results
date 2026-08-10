import FormalConjectures.Util.ProblemImports
example (P : Prop) (h : ¬ P) : False := by
  fail_if_success nomatch h
  exact h (by
    fail_if_success nomatch h
    sorry)
