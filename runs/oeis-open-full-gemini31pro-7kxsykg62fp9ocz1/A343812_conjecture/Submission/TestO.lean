import Mathlib
open Nat Finset

def p (i : ℕ) : ℕ := Nat.nth Nat.Prime i
def S (n : ℕ) : ℕ := (range n).sum p
def a_eval (n : ℕ) : ℕ := (range n).sum (fun i => S n % p i)

#eval a_eval 1
