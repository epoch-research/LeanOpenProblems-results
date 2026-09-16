import Mathlib

def a (n : ℕ) : ℤ :=
  (Finset.range (n + 1)).sum fun k : ℕ =>
    (-4 : ℤ) ^ k * (Nat.choose n k : ℤ) ^ 2 * (Nat.choose (n - k) k : ℤ) ^ 2

def S (n : ℕ) : ℤ := (Finset.range n).sum fun k : ℕ => (20 * (k : ℤ) + 17) * a k

#eval S 5
#eval 5 * (10 * legendreSym 5 (-1) + 7)
