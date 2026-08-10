import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 200000

theorem test_8_0 : False := by
  exact List.Duplicate.elim_singleton

theorem test_8_1 : False := by
  apply List.Duplicate.elim_singleton <;> simp

theorem test_8_2 : False := by
  apply List.Duplicate.elim_singleton <;> norm_num

theorem test_8_3 : False := by
  apply List.Duplicate.elim_singleton <;> aesop

theorem test_8_4 : False := by
  apply List.Duplicate.elim_singleton <;> (first | infer_instance | norm_num | simp | aesop)

theorem test_8_5 : False := by
  refine List.Duplicate.elim_singleton ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> (first | infer_instance | norm_num | simp | aesop)

