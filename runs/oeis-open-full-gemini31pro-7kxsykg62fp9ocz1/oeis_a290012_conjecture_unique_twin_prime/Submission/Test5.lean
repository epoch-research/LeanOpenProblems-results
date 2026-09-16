import Mathlib

def nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime n
#eval nthPrime 0
#eval nthPrime 1
#eval nthPrime 2
