import Mathlib

lemma test_2400 (q1 q2 : ℤ) (H1 : q1 = 1 ∨ q1 = 2 ∨ q1 = 3 ∨ q1 = 4 ∨ q1 = 5 ∨ q1 = 6 ∨ q1 = 7 ∨ q1 = 8 ∨ q1 = 9 ∨ q1 = 10 ∨ q1 = 11 ∨ q1 = 12 ∨ q1 = 13 ∨ q1 = 14 ∨ q1 = 15 ∨ q1 = 16 ∨ q1 = 17 ∨ q1 = 18 ∨ q1 = 19 ∨ q1 = 20)
  (H2 : q2 = 1 ∨ q2 = 2 ∨ q2 = 3 ∨ q2 = 4 ∨ q2 = 5 ∨ q2 = 6 ∨ q2 = 7 ∨ q2 = 8 ∨ q2 = 9 ∨ q2 = 10 ∨ q2 = 11 ∨ q2 = 12 ∨ q2 = 13 ∨ q2 = 14 ∨ q2 = 15 ∨ q2 = 16 ∨ q2 = 17 ∨ q2 = 18 ∨ q2 = 19 ∨ q2 = 20) :
  q1 + q2 = q2 + q1 := by
  rcases H1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases H2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  omega
