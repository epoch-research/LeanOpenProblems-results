import FormalConjectures.Util.ProblemImports

example (n : ℕ) : n = 1 := by
  fail_if_success congr
  fail_if_success simp
  fail_if_success exact Subsingleton.elim n 1
  fail_if_success apply Subsingleton.elim
  omega

example : (True : Prop) = False := by
  fail_if_success congr
  fail_if_success simp
  fail_if_success exact Subsingleton.elim (True : Prop) False
  fail_if_success apply Subsingleton.elim
  exact False.elim (by contradiction)
