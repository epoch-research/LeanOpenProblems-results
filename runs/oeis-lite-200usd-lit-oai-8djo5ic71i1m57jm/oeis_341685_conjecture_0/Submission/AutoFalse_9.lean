import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 200000

theorem test_9_0 : False := by
  exact PrincipalSeg.irrefl

theorem test_9_1 : False := by
  apply PrincipalSeg.irrefl <;> simp

theorem test_9_2 : False := by
  apply PrincipalSeg.irrefl <;> norm_num

theorem test_9_3 : False := by
  apply PrincipalSeg.irrefl <;> aesop

theorem test_9_4 : False := by
  apply PrincipalSeg.irrefl <;> (first | infer_instance | norm_num | simp | aesop)

theorem test_9_5 : False := by
  refine PrincipalSeg.irrefl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> (first | infer_instance | norm_num | simp | aesop)

