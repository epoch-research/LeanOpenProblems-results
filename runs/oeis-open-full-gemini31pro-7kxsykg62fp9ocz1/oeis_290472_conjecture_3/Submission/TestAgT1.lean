import Submission.Spec

theorem a_gt_1_of_sols (n x1 y1 z1 x2 y2 z2 : Nat)
  (h1 : x1 > 0) (h_eq1 : x1 * x1 + 3 * y1 * y1 + 7 * z1 * z1 = 6 * n + 1)
  (h2 : x2 > 0) (h_eq2 : x2 * x2 + 3 * y2 * y2 + 7 * z2 * z2 = 6 * n + 1)
  (h_diff : x1 ≠ x2 ∨ y1 ≠ y2 ∨ z1 ≠ z2) :
  a n > 1 := by
  sorry
