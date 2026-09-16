import Mathlib

open Nat Finset Int

def a (n : ℕ) : ℤ :=
  (Finset.range (n + 1)).sum fun k : ℕ =>
    (-4 : ℤ) ^ k * (choose n k : ℤ) ^ 2 * (choose (n - k) k : ℤ) ^ 2

#eval! a 1
#eval! a 2
#eval! a 3
#eval! a 4
#eval! a 5

def S (n : ℕ) : ℤ := (Finset.range n).sum fun k : ℕ => (20 * k + 17) * a k

#eval! S 1
#eval! S 2
#eval! S 3
#eval! S 4
#eval! S 5
#eval! S 6
#eval! S 7
