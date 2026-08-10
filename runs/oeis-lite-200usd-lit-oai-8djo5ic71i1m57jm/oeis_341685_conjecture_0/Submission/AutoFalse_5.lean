import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 200000

theorem test_5_0 : False := by
  exact Lean.Grind.Linarith.lt_unsat

theorem test_5_1 : False := by
  apply Lean.Grind.Linarith.lt_unsat <;> simp

theorem test_5_2 : False := by
  apply Lean.Grind.Linarith.lt_unsat <;> norm_num

theorem test_5_3 : False := by
  apply Lean.Grind.Linarith.lt_unsat <;> aesop

theorem test_5_4 : False := by
  apply Lean.Grind.Linarith.lt_unsat <;> (first | infer_instance | norm_num | simp | aesop)

theorem test_5_5 : False := by
  refine Lean.Grind.Linarith.lt_unsat ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> (first | infer_instance | norm_num | simp | aesop)

