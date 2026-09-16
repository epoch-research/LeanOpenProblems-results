import Mathlib

open Rat Nat

def a_comp (n : ℕ) : ℕ :=
  if h : n = 0 then 0
  else
    let n_q : ℚ := n
    let B_nm1 : ℚ := bernoulli (n - 1)
    let F_n : ℚ := (B_nm1.num : ℚ) / n_q + (B_nm1.den : ℚ) / (n_q * n_q)
    F_n.den

def main : IO Unit := do
  IO.println s!"a={a_comp 15}"
