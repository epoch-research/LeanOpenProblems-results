import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 200000

theorem test_2_0 : False := by
  exact Nat.not_succ_le_zero

theorem test_2_1 : False := by
  apply Nat.not_succ_le_zero <;> simp

theorem test_2_2 : False := by
  apply Nat.not_succ_le_zero <;> norm_num

theorem test_2_3 : False := by
  apply Nat.not_succ_le_zero <;> aesop

theorem test_2_4 : False := by
  apply Nat.not_succ_le_zero <;> (first | infer_instance | norm_num | simp | aesop)

theorem test_2_5 : False := by
  refine Nat.not_succ_le_zero ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> (first | infer_instance | norm_num | simp | aesop)

