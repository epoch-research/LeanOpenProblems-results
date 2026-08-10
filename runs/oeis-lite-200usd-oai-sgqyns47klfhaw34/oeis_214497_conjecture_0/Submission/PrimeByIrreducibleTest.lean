import FormalConjectures.Util.ProblemImports
open Nat

example (n k : ℕ) : Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) := by
  change Irreducible ((3 ^ n - k) * (2 ^ n) - 1)
  exact?
