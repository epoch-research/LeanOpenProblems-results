import FormalConjectures.Util.ProblemImports

set_option exponentiation.threshold 3000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 50

open Nat

theorem oeis_378143_conjecture_claim :
  ∀ (n : ℕ),
    Nat.Prime (10 ^ (2 ^ n) + 1) →
      Nat.Prime (4 ^ (2 ^ n) + 1) ∨ Nat.Prime (6 ^ (2 ^ n) + 1) := by
  intro n
  rcases n with _ | _ | _ | _ | n
  · intro _
    left
    decide
  · intro _
    left
    decide
  · intro h
    exfalso
    apply Nat.not_prime_of_dvd_of_ne (m := 73) at h
    · exact h
    · decide
    · decide
    · decide
  · intro h
    exfalso
    apply Nat.not_prime_of_dvd_of_ne (m := 17) at h
    · exact h
    · decide
    · decide
    · decide
  · sorry
