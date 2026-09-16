import Mathlib

example (x : ℤ) (hx : 0 ≤ x) : (x.toNat : ℤ) = x := by
  exact Int.toNat_of_nonneg hx
