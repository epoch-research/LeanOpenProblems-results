import FormalConjectures.Util.ProblemImports

set_option exponentiation.threshold 1500000
set_option maxRecDepth 1500000

open Nat Set

theorem oeis_378143_conjecture_claim :
  ∀ (n : ℕ),
    Nat.Prime (10 ^ (2 ^ n) + 1) →
      Nat.Prime (4 ^ (2 ^ n) + 1) ∨ Nat.Prime (6 ^ (2 ^ n) + 1) := by
  intro n
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n
  · intro _
    left
    decide
  · intro _
    left
    decide
  · intro _
    left
    decide
  · intro _
    left
    decide
  all_goals sorry
