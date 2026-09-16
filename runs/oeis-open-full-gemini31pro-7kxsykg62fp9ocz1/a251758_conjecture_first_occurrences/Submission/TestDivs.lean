import Mathlib

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem test_divs : (Nat.divisors 6678671).card = 32 := by decide
