import Submission.Spec
open Nat Finset BigOperators

theorem A297707_val : ∀ n, 2 < n → n ≤ 250 → ¬ IsComposite (A297707 n - Nat.prevPrime (A297707 n)) := by
  intro n h_gt_2 h_le_250
  revert h_gt_2 h_le_250
  revert n
  sorry

