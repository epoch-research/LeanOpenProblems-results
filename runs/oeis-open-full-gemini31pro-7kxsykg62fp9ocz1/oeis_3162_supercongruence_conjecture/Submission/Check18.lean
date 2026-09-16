import Mathlib

open Nat Finset

def A003162 (n : ℕ) : ℕ :=
  let numerator := (Finset.range (n / 2 + 1)).sum fun k =>
    let c_k := n.choose k
    let c_k_prev := if k = 0 then 0 else n.choose (k - 1)
    (c_k - c_k_prev) ^ 3
  let denominator := n.choose (n / 2)
  numerator / denominator

def main : IO Unit := do
  let lst := (List.range 20).map A003162
  IO.println lst

#eval main
