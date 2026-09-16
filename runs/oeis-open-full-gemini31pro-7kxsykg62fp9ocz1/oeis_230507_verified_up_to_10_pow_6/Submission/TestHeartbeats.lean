set_option maxHeartbeats 0
set_option maxRecDepth 2000000

def sumLoop (n i acc : Nat) : Nat :=
  match n with
  | 0 => acc
  | k + 1 => sumLoop k (i + 1) (acc + i)

theorem t1 : sumLoop 100000 0 0 = 4999950000 := by decide
