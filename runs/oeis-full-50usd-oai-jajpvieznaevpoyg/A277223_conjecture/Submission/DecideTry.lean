import FormalConjectures.Util.ProblemImports
open Nat Set
private def sum_digits_10 (m : ℕ) : ℕ := (Nat.digits 10 m).sum
noncomputable def A277223 (n : ℕ) : ℕ :=
  let valid_multipliers : Set ℕ := { k | k = sum_digits_10 (k * n) }
  sSup valid_multipliers

example (n : ℕ) : Decidable (n > 0 → (A277223 n < 12 → A277223 n = 0 ∨ A277223 n = 9)) := by
  infer_instance
