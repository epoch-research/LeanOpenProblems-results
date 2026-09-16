import Mathlib

open Nat Finset

lemma sum_range_mul_add {R : Type*} [AddCommMonoid R] (n m : ℕ) (f : ℕ → R) :
    ∑ k ∈ range (n * m), f k = ∑ i ∈ range n, ∑ j ∈ range m, f (i * m + j) := by
  induction' n with n ih
  · simp
  · rw [succ_mul, sum_range_add, ih, sum_range_succ]
