import FormalConjectures.Util.ProblemImports

theorem a4_prime : Nat.Prime (2^127 - 1) := by
  exact lucas_lehmer_M127_prime -- wait, I need to find the exact name
