import Submission.Spec

example : a 3 = 49 := by
  unfold a
  norm_num [Finset.sum_Icc, Finset.sum_insert, Finset.sum_singleton]
  
example : a089026 4 = 2 := by
  unfold a089026 Nat.squarePart Nat.squarefreePart
  rfl
