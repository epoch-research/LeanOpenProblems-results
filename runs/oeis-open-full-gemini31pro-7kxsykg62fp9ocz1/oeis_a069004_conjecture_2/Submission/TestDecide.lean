import Mathlib

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

def p : ℕ := 512720^2 + 19^2

theorem p_is_prime : Nat.Prime p := by decide
