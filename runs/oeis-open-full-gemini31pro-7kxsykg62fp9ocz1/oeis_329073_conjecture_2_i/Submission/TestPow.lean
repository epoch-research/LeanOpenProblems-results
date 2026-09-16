import Mathlib

theorem not_pow_0 : ¬ Nat.isPowerOfTwo 0 := by
  rintro ⟨k, hk⟩
  have : 2 ^ k > 0 := Nat.two_pow_pos k
  omega
