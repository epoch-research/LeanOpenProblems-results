import Mathlib

def chunk1 : List ℕ := (List.range 1000).map (· + 1000) |>.filter (fun x => if h : x > 0 then 6678671 % x == 0 else false)

set_option maxHeartbeats 0
set_option maxRecDepth 10000000
theorem t1 : chunk1 = [] := by decide
