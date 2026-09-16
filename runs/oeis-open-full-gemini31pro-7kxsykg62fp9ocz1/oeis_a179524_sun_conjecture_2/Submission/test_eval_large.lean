import Mathlib

open Nat Finset Int

def a (n : ℕ) : ℤ :=
  (Finset.range (n + 1)).sum fun k : ℕ =>
    (-4 : ℤ) ^ k * (choose n k : ℤ) ^ 2 * (choose (n - k) k : ℤ) ^ 2

def S (n : ℕ) : ℤ := (Finset.range n).sum fun k : ℕ => (20 * (k : ℤ) + 17) * a k

#eval! S 13
#eval! show ℤ from let _i : Fact (Nat.Prime 13) := ⟨by decide⟩; 13 * (10 * legendreSym 13 (-1) + 7)

#eval! S 17
#eval! show ℤ from let _i : Fact (Nat.Prime 17) := ⟨by decide⟩; 17 * (10 * legendreSym 17 (-1) + 7)
