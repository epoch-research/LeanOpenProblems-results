import Submission.Test.F_117
def step_exact (k : Nat) (v : Nat) : Nat := step v

def apply_exact (n : Nat) : Nat :=
  let rec loop (k : Nat) (v : Nat) :=
    match k with
    | 0 => v
    | k'+1 => loop k' (step_exact (n - k') v)
  loop n 0

set_option maxHeartbeats 10000000
set_option maxRecDepth 200000
theorem eval_fast : apply_exact 117999 = v_117999 := by rfl
