import FormalConjectures.Util.ProblemImports
import Mathlib

open Nat Finset ZMod

theorem one_add_mul_pow_eq_one_add_mul_of_sq_eq_zero {R : Type*} [CommRing R] (p : R) (hp : p ^ 2 = 0) (k : ℕ) :
    (1 + p) ^ k = 1 + k * p := by
  induction' k with k ih
  · simp
  · rw [pow_succ, ih]
    calc (1 + (k : R) * p) * (1 + p)
      _ = 1 + p + k * p + k * p^2 := by ring
      _ = 1 + p + k * p + k * 0 := by rw [hp]
      _ = 1 + (k + 1 : R) * p := by ring
      _ = 1 + (k + 1 : ℕ) * p := by push_cast; rfl
