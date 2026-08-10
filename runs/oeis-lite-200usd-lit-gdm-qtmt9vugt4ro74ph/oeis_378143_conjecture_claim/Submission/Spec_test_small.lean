import FormalConjectures.Util.ProblemImports

set_option exponentiation.threshold 256
set_option maxRecDepth 10000

open Nat Set

theorem oeis_378143_conjecture_claim :
  ∀ (n : ℕ),
    Nat.Prime (10 ^ (2 ^ n) + 1) →
      Nat.Prime (4 ^ (2 ^ n) + 1) ∨ Nat.Prime (6 ^ (2 ^ n) + 1) := by
  intro n
  rcases n with _ | _ | _ | _ | n
  · intro _
    left
    change Nat.Prime 5
    decide
  · intro _
    left
    change Nat.Prime 17
    decide
  · intro _
    left
    change Nat.Prime 257
    decide
  · intro _
    left
    change Nat.Prime 65537
    decide
  · sorry
