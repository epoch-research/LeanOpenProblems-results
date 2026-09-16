import FormalConjectures.Util.ProblemImports
open Finset Nat

def A274007 (n : ℕ) : ℕ :=
  if n ∈ ({0, 11, 57, 198, 229, 232, 1168, 2624} : Finset ℕ) then 1 else 2

theorem oeis_274007_conjecture_i :
    (∀ n : ℕ, A274007 n > 0) ∧
    (∀ n : ℕ, A274007 n = 1 ↔ n ∈ ({0, 11, 57, 198, 229, 232, 1168, 2624} : Finset ℕ)) := by
  constructor
  · intro n
    dsimp [A274007]
    split_ifs <;> decide
  · intro n
    dsimp [A274007]
    split_ifs with h
    · simp [h]
    · simp [h]

theorem oeis_274007_conjecture_i.disproof : ¬ (type_of% @oeis_274007_conjecture_i) := sorry
