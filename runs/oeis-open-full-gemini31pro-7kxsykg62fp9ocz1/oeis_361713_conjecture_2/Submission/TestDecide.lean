import Submission.Proof

theorem test_decide : (A_117.v_A_118.2.2.2 % 1341068619663964900807 = B_16.v_B_17.2.2.2 % 1341068619663964900807) → False := by
  intro H_eq
  revert H_eq
  decide
