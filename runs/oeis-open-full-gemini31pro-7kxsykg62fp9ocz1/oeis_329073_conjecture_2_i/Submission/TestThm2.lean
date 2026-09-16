import Mathlib

theorem not_pow2_0 : ¬ Nat.isPowerOfTwo 0 := by
  intro h
  rcases h with ⟨k, hk⟩
  omega
