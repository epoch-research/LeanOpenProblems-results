import FormalConjectures.Util.ProblemImports

set_option exponentiation.threshold 256
set_option maxRecDepth 10000

open Nat

theorem oeis_378143_conjecture_claim :
  ∀ (n : ℕ),
    Nat.Prime (10 ^ (2 ^ n) + 1) →
      Nat.Prime (4 ^ (2 ^ n) + 1) ∨ Nat.Prime (6 ^ (2 ^ n) + 1) := by
  intro n
  rcases n with _ | n
  · sorry
  rcases n with _ | n
  · sorry
  rcases n with _ | n
  · sorry
  rcases n with _ | n
  · sorry
  · sorry
