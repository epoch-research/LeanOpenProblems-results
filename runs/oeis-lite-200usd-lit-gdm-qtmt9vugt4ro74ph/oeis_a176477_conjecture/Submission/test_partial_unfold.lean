import Mathlib

partial def f (n : ℕ) : ℚ :=
  match n with
  | 0 => 0
  | k + 1 => f k + 1

theorem f_zero : f 0 = 0 := by
  unfold f
  rfl
