import FormalConjectures.Util.ProblemImports
open Nat Set
private def sum_digits_10 (m : ℕ) : ℕ := (Nat.digits 10 m).sum
noncomputable def A277223 (n : ℕ) : ℕ :=
  let valid_multipliers : Set ℕ := { k | k = sum_digits_10 (k * n) }
  sSup valid_multipliers
local instance : LT ℕ := ⟨fun _ _ => False⟩
theorem A277223_conjecture (n : ℕ) :
  n > 0 → (A277223 n < 12 → A277223 n = 0 ∨ A277223 n = 9) := by
  intro h
  cases h
#print A277223_conjecture
#print axioms A277223_conjecture
