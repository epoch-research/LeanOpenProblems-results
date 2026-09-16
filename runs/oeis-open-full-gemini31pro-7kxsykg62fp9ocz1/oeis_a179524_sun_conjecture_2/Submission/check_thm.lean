import Mathlib

open Nat Finset Int

def a (n : ℕ) : ℤ :=
  (Finset.range (n + 1)).sum fun k : ℕ =>
    (-4 : ℤ) ^ k * (choose n k : ℤ) ^ 2 * (choose (n - k) k : ℤ) ^ 2

def S (n : ℕ) : ℤ := (Finset.range n).sum fun k : ℕ => (20 * k + 17) * a k

def check1 (n : ℕ) : Bool :=
  if n = 0 then true else (S n) % (n : ℤ) == 0

def check2 (p : ℕ) : Bool :=
  if p = 2 then true
  else if Nat.Prime p then
    let L : ℤ := if p % 4 == 1 then 1 else -1
    (S p - p * (10 * L + 7)) % (p * p : ℤ) == 0
  else true

#eval! (List.range 50).all check1
#eval! (List.range 50).all check2
