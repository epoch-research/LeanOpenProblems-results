import Mathlib

open Nat Finset Int

def a (n : ℕ) : ℤ :=
  (Finset.range (n + 1)).sum fun k : ℕ =>
    (-4 : ℤ) ^ k * (choose n k : ℤ) ^ 2 * (choose (n - k) k : ℤ) ^ 2

def S (n : ℕ) : ℤ := (Finset.range n).sum fun k : ℕ => (20 * (k : ℤ) + 17) * a k

#eval! S 3
#eval! show ℤ from let _i : Fact (Nat.Prime 3) := ⟨by decide⟩; 3 * (10 * legendreSym 3 (-1) + 7)

#eval! S 5
#eval! show ℤ from let _i : Fact (Nat.Prime 5) := ⟨by decide⟩; 5 * (10 * legendreSym 5 (-1) + 7)

#eval! S 7
#eval! show ℤ from let _i : Fact (Nat.Prime 7) := ⟨by decide⟩; 7 * (10 * legendreSym 7 (-1) + 7)
