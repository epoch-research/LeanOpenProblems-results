import Submission.Spec

theorem a_287_gt_1 : a 287 > 1 := by
  unfold a
  have ha : (20, (21, 0)) ∈ Finset.product (Finset.range (Nat.sqrt (6 * 287 + 1) + 1)) (Finset.product (Finset.range (Nat.sqrt (6 * 287 + 1) + 1)) (Finset.range (Nat.sqrt (6 * 287 + 1) + 1))) := by decide
  sorry
