import FormalConjectures.Util.ProblemImports

set_option exponentiation.threshold 10000000
set_option maxRecDepth 200000

open Nat

theorem oeis_378143_conjecture_claim :
  ∀ (n : ℕ),
    Nat.Prime (10 ^ (2 ^ n) + 1) →
      Nat.Prime (4 ^ (2 ^ n) + 1) ∨ Nat.Prime (6 ^ (2 ^ n) + 1) := by
  intro n
  rcases n with _ | n
  · intro _
    left
    decide
  rcases n with _ | n
  · intro _
    left
    decide
  rcases n with _ | n
  · intro _
    left
    decide
  rcases n with _ | n
  · intro _
    left
    decide
  rcases n with _ | n
  · intro h
    exfalso
    have hdvd : 353 ∣ 10 ^ (2 ^ 4) + 1 := by
      rw [← ZMod.natCast_eq_zero_iff]
      have : (10 : ZMod 353) ^ (2 ^ 4) + 1 = 0 := by
        reduce_mod_char
      exact_mod_cast this
    have h_lt : 353 < 10 ^ (2 ^ 4) + 1 := by decide
    apply Nat.not_prime_of_dvd_of_ne (m := 353) at h
    · exact h
    · exact hdvd
    · decide
    · exact Nat.ne_of_lt h_lt
  · sorry
