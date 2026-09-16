import Mathlib

def is_perfect_cube (k : ℕ) : Prop :=
  ∃ m : ℕ, m ^ 3 = k

-- Let's just check the syntax
