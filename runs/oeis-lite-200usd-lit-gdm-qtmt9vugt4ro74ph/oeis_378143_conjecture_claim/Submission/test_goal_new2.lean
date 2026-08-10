import FormalConjectures.Util.ProblemImports

open Nat

lemma case_0 : Nat.Prime (10 ^ (2 ^ 0) + 1) → Nat.Prime (4 ^ (2 ^ 0) + 1) ∨ Nat.Prime (6 ^ (2 ^ 0) + 1) := sorry
lemma case_1 : Nat.Prime (10 ^ (2 ^ 1) + 1) → Nat.Prime (4 ^ (2 ^ 1) + 1) ∨ Nat.Prime (6 ^ (2 ^ 1) + 1) := sorry
lemma case_2 : Nat.Prime (10 ^ (2 ^ 2) + 1) → Nat.Prime (4 ^ (2 ^ 2) + 1) ∨ Nat.Prime (6 ^ (2 ^ 2) + 1) := sorry
lemma case_3 : Nat.Prime (10 ^ (2 ^ 3) + 1) → Nat.Prime (4 ^ (2 ^ 3) + 1) ∨ Nat.Prime (6 ^ (2 ^ 3) + 1) := sorry
lemma case_4 : Nat.Prime (10 ^ (2 ^ 4) + 1) → Nat.Prime (4 ^ (2 ^ 4) + 1) ∨ Nat.Prime (6 ^ (2 ^ 4) + 1) := sorry
lemma case_5 : Nat.Prime (10 ^ (2 ^ 5) + 1) → Nat.Prime (4 ^ (2 ^ 5) + 1) ∨ Nat.Prime (6 ^ (2 ^ 5) + 1) := sorry
lemma case_6 : Nat.Prime (10 ^ (2 ^ 6) + 1) → Nat.Prime (4 ^ (2 ^ 6) + 1) ∨ Nat.Prime (6 ^ (2 ^ 6) + 1) := sorry
lemma case_7 : Nat.Prime (10 ^ (2 ^ 7) + 1) → Nat.Prime (4 ^ (2 ^ 7) + 1) ∨ Nat.Prime (6 ^ (2 ^ 7) + 1) := sorry
lemma case_8 : Nat.Prime (10 ^ (2 ^ 8) + 1) → Nat.Prime (4 ^ (2 ^ 8) + 1) ∨ Nat.Prime (6 ^ (2 ^ 8) + 1) := sorry
lemma case_9 : Nat.Prime (10 ^ (2 ^ 9) + 1) → Nat.Prime (4 ^ (2 ^ 9) + 1) ∨ Nat.Prime (6 ^ (2 ^ 9) + 1) := sorry
lemma case_10 : Nat.Prime (10 ^ (2 ^ 10) + 1) → Nat.Prime (4 ^ (2 ^ 10) + 1) ∨ Nat.Prime (6 ^ (2 ^ 10) + 1) := sorry
lemma case_11 : Nat.Prime (10 ^ (2 ^ 11) + 1) → Nat.Prime (4 ^ (2 ^ 11) + 1) ∨ Nat.Prime (6 ^ (2 ^ 11) + 1) := sorry
lemma case_12 : Nat.Prime (10 ^ (2 ^ 12) + 1) → Nat.Prime (4 ^ (2 ^ 12) + 1) ∨ Nat.Prime (6 ^ (2 ^ 12) + 1) := sorry
lemma case_13 : Nat.Prime (10 ^ (2 ^ 13) + 1) → Nat.Prime (4 ^ (2 ^ 13) + 1) ∨ Nat.Prime (6 ^ (2 ^ 13) + 1) := sorry
lemma case_14 : Nat.Prime (10 ^ (2 ^ 14) + 1) → Nat.Prime (4 ^ (2 ^ 14) + 1) ∨ Nat.Prime (6 ^ (2 ^ 14) + 1) := sorry
lemma case_15 : Nat.Prime (10 ^ (2 ^ 15) + 1) → Nat.Prime (4 ^ (2 ^ 15) + 1) ∨ Nat.Prime (6 ^ (2 ^ 15) + 1) := sorry
lemma case_16 : Nat.Prime (10 ^ (2 ^ 16) + 1) → Nat.Prime (4 ^ (2 ^ 16) + 1) ∨ Nat.Prime (6 ^ (2 ^ 16) + 1) := sorry
lemma case_17 : Nat.Prime (10 ^ (2 ^ 17) + 1) → Nat.Prime (4 ^ (2 ^ 17) + 1) ∨ Nat.Prime (6 ^ (2 ^ 17) + 1) := sorry
lemma case_18 : Nat.Prime (10 ^ (2 ^ 18) + 1) → Nat.Prime (4 ^ (2 ^ 18) + 1) ∨ Nat.Prime (6 ^ (2 ^ 18) + 1) := sorry
lemma case_19 : Nat.Prime (10 ^ (2 ^ 19) + 1) → Nat.Prime (4 ^ (2 ^ 19) + 1) ∨ Nat.Prime (6 ^ (2 ^ 19) + 1) := sorry
lemma case_20 : Nat.Prime (10 ^ (2 ^ 20) + 1) → Nat.Prime (4 ^ (2 ^ 20) + 1) ∨ Nat.Prime (6 ^ (2 ^ 20) + 1) := sorry
lemma case_22 : Nat.Prime (10 ^ (2 ^ 22) + 1) → Nat.Prime (4 ^ (2 ^ 22) + 1) ∨ Nat.Prime (6 ^ (2 ^ 22) + 1) := sorry

theorem oeis_378143_conjecture_claim :
  ∀ (n : ℕ),
    Nat.Prime (10 ^ (2 ^ n) + 1) →
      Nat.Prime (4 ^ (2 ^ n) + 1) ∨ Nat.Prime (6 ^ (2 ^ n) + 1) := by
  intro n
  rcases n with _ | n
  · exact case_0
  rcases n with _ | n
  · exact case_1
  rcases n with _ | n
  · exact case_2
  rcases n with _ | n
  · exact case_3
  rcases n with _ | n
  · exact case_4
  rcases n with _ | n
  · exact case_5
  rcases n with _ | n
  · exact case_6
  rcases n with _ | n
  · exact case_7
  rcases n with _ | n
  · exact case_8
  rcases n with _ | n
  · exact case_9
  rcases n with _ | n
  · exact case_10
  rcases n with _ | n
  · exact case_11
  rcases n with _ | n
  · exact case_12
  rcases n with _ | n
  · exact case_13
  rcases n with _ | n
  · exact case_14
  rcases n with _ | n
  · exact case_15
  rcases n with _ | n
  · exact case_16
  rcases n with _ | n
  · exact case_17
  rcases n with _ | n
  · exact case_18
  rcases n with _ | n
  · exact case_19
  rcases n with _ | n
  · exact case_20
  rcases n with _ | n
  · sorry -- case 21
  rcases n with _ | n
  · exact case_22
  · sorry -- case >= 23
