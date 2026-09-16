import Mathlib

open Nat

def countPrimesFast (n : ℕ) : ℕ :=
  (List.range n).foldl (fun c k => if k ≥ 2 ∧ k.minFac == k then c + 1 else c) 0

lemma count_is_990 : countPrimesFast 7841 = 990 := by decide
