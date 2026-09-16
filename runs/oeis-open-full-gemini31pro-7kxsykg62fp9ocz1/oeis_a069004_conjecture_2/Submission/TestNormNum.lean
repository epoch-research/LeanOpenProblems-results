import Mathlib

set_option maxHeartbeats 0
set_option maxRecDepth 2000000

def p : ℕ := 512720^2 + 21^2
theorem p_prime : Nat.Prime p := by decide
