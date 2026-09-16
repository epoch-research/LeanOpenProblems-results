import Mathlib

open Nat Finset

def A003162 (n : ℕ) : ℕ :=
  let numerator := (Finset.range (n / 2 + 1)).sum fun k =>
    let c_k := n.choose k
    let c_k_prev := if k = 0 then 0 else n.choose (k - 1)
    (c_k - c_k_prev) ^ 3
  let denominator := n.choose (n / 2)
  numerator / denominator

def A003162.b (n : ℕ) : ℕ := A003162 (2 * n - 1)

#eval A003162.b 1
#eval A003162.b 2
#eval A003162.b 3
#eval A003162.b 4
#eval A003162.b 5
