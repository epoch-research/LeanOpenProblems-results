import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 200000

theorem test_1_0 : False := by
  exact Ne.irrefl

theorem test_1_1 : False := by
  apply Ne.irrefl <;> simp

theorem test_1_2 : False := by
  apply Ne.irrefl <;> norm_num

theorem test_1_3 : False := by
  apply Ne.irrefl <;> aesop

theorem test_1_4 : False := by
  apply Ne.irrefl <;> (first | infer_instance | norm_num | simp | aesop)

theorem test_1_5 : False := by
  refine Ne.irrefl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> (first | infer_instance | norm_num | simp | aesop)

