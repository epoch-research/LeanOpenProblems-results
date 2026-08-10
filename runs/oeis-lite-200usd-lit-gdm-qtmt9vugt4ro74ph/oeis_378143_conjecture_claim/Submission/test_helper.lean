import FormalConjectures.Util.ProblemImports

set_option exponentiation.threshold 100000
set_option maxRecDepth 10000

open Nat

lemma case_0 : Nat.Prime (10 ^ (2 ^ 0) + 1) → Nat.Prime (4 ^ (2 ^ 0) + 1) ∨ Nat.Prime (6 ^ (2 ^ 0) + 1) := by
  intro _
  left
  decide

lemma case_1 : Nat.Prime (10 ^ (2 ^ 1) + 1) → Nat.Prime (4 ^ (2 ^ 1) + 1) ∨ Nat.Prime (6 ^ (2 ^ 1) + 1) := by
  intro _
  left
  decide

lemma case_2 : Nat.Prime (10 ^ (2 ^ 2) + 1) → Nat.Prime (4 ^ (2 ^ 2) + 1) ∨ Nat.Prime (6 ^ (2 ^ 2) + 1) := by
  intro _
  left
  decide

theorem oeis_378143_conjecture_claim :
  ∀ (n : ℕ),
    Nat.Prime (10 ^ (2 ^ n) + 1) →
      Nat.Prime (4 ^ (2 ^ n) + 1) ∨ Nat.Prime (6 ^ (2 ^ n) + 1) := by
  intro n
  rcases n with _ | _ | _ | n
  · exact case_0
  · exact case_1
  · exact case_2
  · sorry
