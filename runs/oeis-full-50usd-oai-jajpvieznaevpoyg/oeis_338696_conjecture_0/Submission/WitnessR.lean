import FormalConjectures.Util.ProblemImports
open Nat BigOperators Finset

example {m r : ℕ} (h : r * r = m) : m.sqrt * m.sqrt = m := by
  rw [← h, Nat.sqrt_eq]

