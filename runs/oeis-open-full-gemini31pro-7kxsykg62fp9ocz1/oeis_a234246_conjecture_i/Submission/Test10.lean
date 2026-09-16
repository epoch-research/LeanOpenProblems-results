import Mathlib

open Finset Nat

def a (n : ℕ) : ℕ :=
  (Ico 1 n).sum fun k =>
    let m := k * Nat.totient (n - k) + 1
    if Nat.sqrt m * Nat.sqrt m = m then 1 else 0

def S : Finset ℕ := {4, 5, 8, 9, 12, 13, 24, 33, 49}

def check (n : ℕ) : Bool :=
  let c1 := if 0 < n ∧ ¬ (n ∣ 6) then a n > 0 else true
  let c2 := (a n = 1) == (n ∈ S)
  c1 && c2

#eval (List.range 100).all check
