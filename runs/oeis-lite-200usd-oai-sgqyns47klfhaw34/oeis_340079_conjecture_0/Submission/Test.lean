import FormalConjectures.Util.ProblemImports

open Nat BigOperators Finset

def a (n : ℕ) : ℕ :=
  let A018804_n : ℕ := (Finset.Ico 1 (n + 1)).sum fun k => Nat.gcd k n
  n / Nat.gcd n (1 + A018804_n)

example (n : ℕ) : a n = 1 ↔ (n = 1 ∨ Nat.Prime n) := by
  simp [a]
