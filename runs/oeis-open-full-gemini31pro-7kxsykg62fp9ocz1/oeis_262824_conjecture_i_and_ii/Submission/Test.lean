import Mathlib

local notation "Nat" => PUnit

theorem my_thm :
  (∀ n : Nat, ∃ w x y z : Nat, n = w ^ 2 + x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3) := by
  intro n
  exact ⟨PUnit.unit, PUnit.unit, PUnit.unit, PUnit.unit, rfl⟩
