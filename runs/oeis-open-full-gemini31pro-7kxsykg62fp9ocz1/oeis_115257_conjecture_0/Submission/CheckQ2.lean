import Submission.Spec
import Mathlib
open Polynomial

lemma q2_eq : poly_A115257_Q 2 = C (12:ℚ) * X^2 + C (2:ℚ) * X + 1 := by
  dsimp [poly_A115257_Q]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  simp [Nat.centralBinom]
  have : C ((1:ℚ) / 1) = 1 := by norm_num
  rw [this]
  have : C ((4:ℚ) / 2) = C 2 := by norm_num
  rw [this]
  have : C ((36:ℚ) / 3) = C 12 := by norm_num
  rw [this]
  ring
