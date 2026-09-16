import Submission.Test.F_117
def apply_exact (n : Nat) (v : Nat) : Nat :=
  match n with
  | 0 => v
  | k+1 => apply_exact k (step v)

set_option maxHeartbeats 10000000
set_option maxRecDepth 200000
theorem eval_fast : apply_exact 117999 0 = v_117999 := by rfl
