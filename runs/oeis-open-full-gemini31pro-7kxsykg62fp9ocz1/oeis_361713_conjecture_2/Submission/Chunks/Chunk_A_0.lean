import Submission.ExactDef
set_option maxRecDepth 2000000
def val_A_0 : Nat × Nat × Nat := (1, 1, 1)
theorem eq_A_0 : apply_exact 117649 0 0 val_A_0 = val_A_0 := rfl
