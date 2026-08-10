import FormalConjectures.Util.ProblemImports

theorem test_self (n : Nat) : n = n := by
  exact test_self n
