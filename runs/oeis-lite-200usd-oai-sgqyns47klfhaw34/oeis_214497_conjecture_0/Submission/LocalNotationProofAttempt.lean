import FormalConjectures.Util.ProblemImports
open Nat

example (n : ℕ) (hn : n > 0) :
    ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1) := by
  -- Local notation inside proof cannot affect elaborated target.
  local notation "X" => ((3 ^ n - (0:ℕ)) * (2 ^ n) - 1)
  use 0
  change Nat.Prime X ∧ Nat.Prime (((3 ^ n - (0:ℕ)) * (2 ^ n)) + 1)
  exact?
