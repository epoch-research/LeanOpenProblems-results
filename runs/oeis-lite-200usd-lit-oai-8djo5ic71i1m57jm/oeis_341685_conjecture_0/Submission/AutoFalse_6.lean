import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 200000

theorem test_6_0 : False := by
  exact CharP.false_of_nontrivial_of_char_one

theorem test_6_1 : False := by
  apply CharP.false_of_nontrivial_of_char_one <;> simp

theorem test_6_2 : False := by
  apply CharP.false_of_nontrivial_of_char_one <;> norm_num

theorem test_6_3 : False := by
  apply CharP.false_of_nontrivial_of_char_one <;> aesop

theorem test_6_4 : False := by
  apply CharP.false_of_nontrivial_of_char_one <;> (first | infer_instance | norm_num | simp | aesop)

theorem test_6_5 : False := by
  refine CharP.false_of_nontrivial_of_char_one ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> (first | infer_instance | norm_num | simp | aesop)

