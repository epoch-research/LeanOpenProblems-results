import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 200000

theorem test_3_0 : False := by
  exact IsEmpty.false

theorem test_3_1 : False := by
  apply IsEmpty.false <;> simp

theorem test_3_2 : False := by
  apply IsEmpty.false <;> norm_num

theorem test_3_3 : False := by
  apply IsEmpty.false <;> aesop

theorem test_3_4 : False := by
  apply IsEmpty.false <;> (first | infer_instance | norm_num | simp | aesop)

theorem test_3_5 : False := by
  refine IsEmpty.false ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> (first | infer_instance | norm_num | simp | aesop)

