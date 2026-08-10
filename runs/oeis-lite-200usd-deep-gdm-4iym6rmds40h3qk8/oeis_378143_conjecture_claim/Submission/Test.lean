import FormalConjectures.Util.ProblemImports

open Nat Set

theorem test_case_0 :
  Nat.Prime (10 ^ (2 ^ 0) + 1) →
    Nat.Prime (4 ^ (2 ^ 0) + 1) ∨ Nat.Prime (6 ^ (2 ^ 0) + 1) := by
  intro h
  left
  decide

theorem test_case_1 :
  Nat.Prime (10 ^ (2 ^ 1) + 1) →
    Nat.Prime (4 ^ (2 ^ 1) + 1) ∨ Nat.Prime (6 ^ (2 ^ 1) + 1) := by
  intro h
  left
  decide

theorem test_case_2 :
  Nat.Prime (10 ^ (2 ^ 2) + 1) →
    Nat.Prime (4 ^ (2 ^ 2) + 1) ∨ Nat.Prime (6 ^ (2 ^ 2) + 1) := by
  intro h
  have hdiv : 73 ∣ 10 ^ (2 ^ 2) + 1 := by decide
  have h1 : 73 ≠ 1 := by decide
  have h2 : 73 ≠ 10 ^ (2 ^ 2) + 1 := by decide
  have h_false : False := by
    have := h.eq_one_or_self_of_dvd 73 hdiv
    rcases this with e1 | e2
    · exact h1 e1
    · exact h2 e2
  exact False.elim h_false

theorem test_case_3 :
  Nat.Prime (10 ^ (2 ^ 3) + 1) →
    Nat.Prime (4 ^ (2 ^ 3) + 1) ∨ Nat.Prime (6 ^ (2 ^ 3) + 1) := by
  intro h
  have hdiv : 17 ∣ 10 ^ (2 ^ 3) + 1 := by decide
  have h1 : 17 ≠ 1 := by decide
  have h2 : 17 ≠ 10 ^ (2 ^ 3) + 1 := by decide
  have h_false : False := by
    have := h.eq_one_or_self_of_dvd 17 hdiv
    rcases this with e1 | e2
    · exact h1 e1
    · exact h2 e2
  exact False.elim h_false

