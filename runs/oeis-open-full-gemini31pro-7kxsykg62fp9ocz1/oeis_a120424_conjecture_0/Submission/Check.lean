import Mathlib

def F_C_bounds (F : ℕ) (C : ℤ) : Bool :=
  F ≥ 91 ∧ 3 * (F : ℤ) ≥ 5 * C ∧ 3 * (F : ℤ) ≥ -7 * C

-- A simple linear congruential generator or just a loop to generate states
-- Actually we can just write the BFS directly!
