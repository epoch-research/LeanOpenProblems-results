import Mathlib

def count_sixes (m : ℕ) : ℕ := (Nat.digits 10 m).count 6

#eval count_sixes (Nat.factorial 130)
#eval count_sixes (Nat.factorial 131)
