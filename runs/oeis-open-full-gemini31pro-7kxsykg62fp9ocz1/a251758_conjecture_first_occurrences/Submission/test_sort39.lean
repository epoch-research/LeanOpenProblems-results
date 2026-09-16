import Mathlib

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem t1 : (Nat.divisors 6678671).card = 32 := by decide
