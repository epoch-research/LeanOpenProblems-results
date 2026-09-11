import FormalConjectures.Util.ProblemImports

open Finset Nat Set

noncomputable def a (n : ℕ) : ℕ :=
  let candidates : Set ℕ :=
    { m : ℕ | 0 < m ∧
      ∃ D : Finset ℕ,
        D ⊆ Nat.divisors m ∧
        D.card = n ∧
        D.sum id = m ∧
        D.lcm id = m }
  sInf candidates

noncomputable def a081512 (n : ℕ) : ℕ :=
  let candidates : Set ℕ :=
    { m : ℕ | 0 < m ∧
      ∃ D : Finset ℕ,
        D ⊆ Nat.divisors m ∧
        D.card = n ∧
        D.sum id = m }
  sInf candidates

theorem oeis_355228_conjecture_0 (n : ℕ) :
  (a n > a081512 n) ↔ (n = 4 ∨ n = 5) := by
  sorry

theorem oeis_355228_conjecture_0.disproof : ¬ (type_of% @oeis_355228_conjecture_0) := by
  sorry
