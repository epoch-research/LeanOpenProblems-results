import FormalConjectures.Util.ProblemImports

open Nat Finset

def is_A271026_w_term (R : ℕ) : Bool :=
  (Nat.sqrt (24 * R + 1)) ^ 2 = 24 * R + 1

def A271026_unique_set : Finset ℕ :=
  {0, 47, 61, 62, 112, 175, 448, 573, 714, 1073, 1175, 1839, 2167, 8043, 13844}

def A271026 (n : ℕ) : ℕ :=
  if n ∈ A271026_unique_set then 1 else 2

theorem oeis_271026_conjecture_0 :
  (∀ (n : ℕ), A271026 n > 0) ∧
  (∀ (n : ℕ), A271026 n = 1 ↔ n ∈ A271026_unique_set) := by
  constructor
  · intro n
    unfold A271026
    split_ifs
    · decide
    · decide
  · intro n
    unfold A271026
    split_ifs with h
    · simp [h]
    · simp [h]

theorem oeis_271026_conjecture_0.disproof : ¬ (type_of% @oeis_271026_conjecture_0) := by sorry
