import FormalConjectures.Util.ProblemImports

open Nat Set

def sum_digits_10 (m : ℕ) : ℕ := (Nat.digits 10 m).sum

noncomputable def A277223 (n : ℕ) : ℕ :=
  let valid_multipliers : Set ℕ := { k | k = sum_digits_10 (k * n) }
  sSup valid_multipliers

theorem A277223_conjecture (n : ℕ) :
  n > 0 → (A277223 n < 12 → A277223 n = 0 ∨ A277223 n = 9) := by
  sorry

theorem A277223_conjecture.disproof : ¬ (type_of% @A277223_conjecture) := by
  sorry
