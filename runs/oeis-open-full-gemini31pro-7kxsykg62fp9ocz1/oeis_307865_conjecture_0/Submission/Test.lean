import Mathlib

theorem one_add_mul_pow_eq_one_add_mul_of_sq_eq_zero {R : Type*} [CommRing R] (p : R) (hp : p ^ 2 = 0) (n : ℕ) :
    (1 + p) ^ n = 1 + n * p := by
  induction' n with n ih
  · simp
  · rw [pow_succ, ih]
    calc (1 + (n : R) * p) * (1 + p)
      _ = 1 + p + n * p + n * p^2 := by ring
      _ = 1 + p + n * p + n * 0 := by rw [hp]
      _ = 1 + (n + 1 : R) * p := by ring
      _ = 1 + (n + 1 : ℕ) * p := by push_cast; rfl

