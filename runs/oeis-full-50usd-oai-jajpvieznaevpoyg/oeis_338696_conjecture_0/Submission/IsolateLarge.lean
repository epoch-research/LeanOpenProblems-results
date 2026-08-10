import FormalConjectures.Util.ProblemImports
open Nat BigOperators Finset
-- minimal mathematical statement needed for the final remaining branch:
example : (∀ n : ℕ, 2000 ≤ n → ∃ x y : ℕ, ∃ z : ℤ,
  x ^ 3 + y ^ 2 + (z * (3 * z + 2)).toNat = n) →
  ∀ n : ℕ, 2000 ≤ n → n ≠ 19 → A338696 n > 0 := by
  intro H n hn _
  rw [A338696_pos_iff_exists_int_z]
  exact H n hn
