import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 200000

theorem test_7_0 : False := by
  exact LT.lt.false

theorem test_7_1 : False := by
  apply LT.lt.false <;> simp

theorem test_7_2 : False := by
  apply LT.lt.false <;> norm_num

theorem test_7_3 : False := by
  apply LT.lt.false <;> aesop

theorem test_7_4 : False := by
  apply LT.lt.false <;> (first | infer_instance | norm_num | simp | aesop)

theorem test_7_5 : False := by
  refine LT.lt.false ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> (first | infer_instance | norm_num | simp | aesop)

