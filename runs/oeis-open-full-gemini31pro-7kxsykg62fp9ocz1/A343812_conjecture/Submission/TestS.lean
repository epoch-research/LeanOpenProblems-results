import Mathlib

open Nat Finset

def S_n (n : ℕ) : ℕ := (range n).sum (fun k => Nat.nth Nat.Prime k)
def a_n (n : ℕ) : ℕ := (range n).sum (fun i => S_n n % (Nat.nth Nat.Prime i))

theorem S_1_is : S_n 1 = 2 := by sorry
theorem a_1_is : a_n 1 = 0 := by sorry
