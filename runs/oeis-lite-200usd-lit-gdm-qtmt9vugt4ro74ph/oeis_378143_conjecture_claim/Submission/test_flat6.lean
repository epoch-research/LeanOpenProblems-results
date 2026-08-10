import FormalConjectures.Util.ProblemImports

set_option exponentiation.threshold 100000
set_option maxRecDepth 10000

open Nat

theorem oeis_378143_conjecture_claim :
  ∀ (n : ℕ),
    Nat.Prime (10 ^ (2 ^ n) + 1) →
      Nat.Prime (4 ^ (2 ^ n) + 1) ∨ Nat.Prime (6 ^ (2 ^ n) + 1) := by
  intro n
  rcases n with _ | n
  · intro _
    left
    change Nat.Prime 5
    decide
  rcases n with _ | n
  · intro _
    left
    change Nat.Prime 17
    decide
  rcases n with _ | n
  · intro _
    left
    change Nat.Prime 257
    decide
  rcases n with _ | n
  · intro _
    left
    change Nat.Prime 65537
    decide
  · sorry
