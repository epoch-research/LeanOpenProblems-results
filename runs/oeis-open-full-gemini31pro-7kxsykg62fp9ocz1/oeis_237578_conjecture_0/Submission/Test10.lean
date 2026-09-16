import Mathlib

def check (n k : ℕ) : Bool :=
  Nat.Prime (Nat.primeCounting (k * n))

#eval check 38 21
