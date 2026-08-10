import Mathlib

lemma rat_int_of_den_one (q : ℚ) (h : q.den = 1) : ∃ (z : ℤ), q = (z : ℚ) := by
  use q.num
  apply Rat.ext
  · simp
  · rw [h]
    rfl
