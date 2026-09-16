import Mathlib

def check (m : ℕ) : Bool :=
  (509203 * (2 ^ m) - 1).Prime

#eval check 1
#eval check 2
#eval check 3
