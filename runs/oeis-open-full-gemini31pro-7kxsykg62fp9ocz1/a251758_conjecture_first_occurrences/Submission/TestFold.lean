import Mathlib

set_option maxHeartbeats 0

theorem test_fold : (List.range 100000).foldl (fun acc x => acc + 1) 0 = 100000 := by decide
