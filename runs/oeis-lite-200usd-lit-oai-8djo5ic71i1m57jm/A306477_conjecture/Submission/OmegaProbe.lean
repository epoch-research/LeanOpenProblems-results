import FormalConjectures.Util.ProblemImports

example (n : Nat) : n = n + 1 := by
  fail_if_success omega
  sorry
example : False := by
  fail_if_success omega
  sorry
example (n : Nat) : n < n := by
  fail_if_success omega
  sorry
