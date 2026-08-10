import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 200000

theorem test_4_0 : False := by
  exact Fintype.false

theorem test_4_1 : False := by
  apply Fintype.false <;> simp

theorem test_4_2 : False := by
  apply Fintype.false <;> norm_num

theorem test_4_3 : False := by
  apply Fintype.false <;> aesop

theorem test_4_4 : False := by
  apply Fintype.false <;> (first | infer_instance | norm_num | simp | aesop)

theorem test_4_5 : False := by
  refine Fintype.false ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> (first | infer_instance | norm_num | simp | aesop)

