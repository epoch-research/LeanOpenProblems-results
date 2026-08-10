import Mathlib

open Nat Finset

def a (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))

partial def pf (k' : ℕ) : (a (6 * (k' + 5))  ≠ 4) ∨ (a (6 * (k' + 5))  = 4) :=
  pf k'

theorem test_thm (k' : ℕ) : (a (6 * (k' + 5))  ≠ 4) ∨ (a (6 * (k' + 5))  = 4) :=
  pf k'

#print axioms test_thm
