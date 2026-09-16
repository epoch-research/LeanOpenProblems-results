import FormalConjectures.Util.ProblemImports

open Nat Set

def sum_digits_10 (m : ℕ) : ℕ := (Nat.digits 10 m).sum

noncomputable def A277223 (n : ℕ) : ℕ :=
  let valid_multipliers : Set ℕ := { k | k = sum_digits_10 (k * n) }
  sSup valid_multipliers

theorem test_a : A277223 1 = 9 := by sorry
