import Mathlib.Data.ZMod.Basic

set_option maxRecDepth 2000000

def N : ℕ := 10 ^ (2 ^ 21) + 1

-- Test a single multiplication of size 2 million digits
theorem test_mul : (10 ^ (2 ^ 20) : ZMod N) ^ 2 = 10 ^ (2 ^ 21) := by
  decide
