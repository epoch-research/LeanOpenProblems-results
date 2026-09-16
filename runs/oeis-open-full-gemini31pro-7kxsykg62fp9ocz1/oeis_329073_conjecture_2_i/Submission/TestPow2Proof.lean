import Mathlib

example : Nat.isPowerOfTwo 1 := ⟨0, rfl⟩
example : Nat.isPowerOfTwo 2 := ⟨1, rfl⟩
example : ¬ Nat.isPowerOfTwo 3 := by
  rintro ⟨k, hk⟩
  revert hk; decide
