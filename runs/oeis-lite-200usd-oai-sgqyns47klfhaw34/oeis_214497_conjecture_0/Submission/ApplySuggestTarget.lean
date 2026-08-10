import FormalConjectures.Util.ProblemImports
open Nat
set_option maxHeartbeats 400000
example (n : ℕ) (hn : n > 0) :
    ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1) := by
  apply?
