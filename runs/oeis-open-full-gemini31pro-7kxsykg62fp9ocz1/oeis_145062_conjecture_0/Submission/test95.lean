import Mathlib

noncomputable def a (n: ℕ) : ℕ := n

theorem foo (n : ℕ) : a n = a ((n:ℤ) + 1 - 1).natAbs := by
  try omega
  try (congr; omega)
  try rfl
