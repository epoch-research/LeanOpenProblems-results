import Mathlib

open Nat BigOperators

def a_comp (n : ℕ) : ℕ :=
  if h : n = 0 then 0
  else
    let n_pred : ℕ := n.pred
    let numerator : ℕ := (2 ^ n_pred) * (Finset.Ico 1 n).prod (fun k => 2 ^ k - 1)
    let denominator : ℕ := n.factorial
    numerator / denominator

def check (n : ℕ) : Bool :=
  n ∣ (a_comp (n - 1) + 2 ^ (n - 2))

#eval check 3
#eval check 4
#eval check 5
#eval check 6
#eval check 7
#eval check 8
#eval check 9
#eval check 10
#eval check 341
