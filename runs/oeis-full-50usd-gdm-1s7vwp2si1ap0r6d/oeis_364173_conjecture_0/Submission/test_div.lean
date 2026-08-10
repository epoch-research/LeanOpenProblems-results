import Mathlib

open Real

theorem test_zmod (a b n : ℤ) : (a ≡ b [ZMOD n]) ↔ n ∣ b - a := by
  exact Int.modEq_iff_dvd









