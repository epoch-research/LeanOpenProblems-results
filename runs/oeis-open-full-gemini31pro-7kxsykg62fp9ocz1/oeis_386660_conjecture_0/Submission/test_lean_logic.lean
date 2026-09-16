import Mathlib

open Nat

def M (n : ℕ) : ℕ := (Finset.range (n + 1)).sup (fun k => min (n.choose k) (2 ^ k))

lemma M_super (n m : ℕ) : M n * M m ≤ M (n + m) := sorry
