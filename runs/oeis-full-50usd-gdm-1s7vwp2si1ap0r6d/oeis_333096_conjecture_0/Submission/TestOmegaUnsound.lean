import Mathlib

theorem omega_unsound (x : ℤ) (h : x = -1) : x / 2 < x := by
  omega

