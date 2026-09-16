import Submission.ExactDef
set_option maxRecDepth 2000000
def val_B_0 : Nat × Nat × Nat := (1, 1, 1)
theorem eq_B_0 : apply_exact 16807 0 0 val_B_0 = val_B_0 := rfl
