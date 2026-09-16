import Mathlib

def P2_condition (m : ℕ) : Bool :=
  m > 0 ∧ (Nat.Prime (2 * m + 1)) ∧ (Nat.Prime (2 * m ^ 4 - 1))

-- This won't easily compile for `#eval` because `Nat.Prime` isn't a simple Bool without `decide`.
