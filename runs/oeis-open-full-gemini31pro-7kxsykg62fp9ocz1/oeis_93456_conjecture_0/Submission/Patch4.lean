import Mathlib
open Nat Finset

lemma test (A B C D E : ℕ) (H_div1 : A = B) (H_sum_le : C ≤ B) (H_sum_eq : C = D) (H_sum_px : E ≤ D) : E ≤ A := by
  rw [H_div1]
  rw [← H_sum_eq] at H_sum_px
  omega

