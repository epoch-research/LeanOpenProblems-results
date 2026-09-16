import Mathlib

open Nat Finset

def A003162 (n : ℕ) : ℕ :=
  let numerator := (Finset.range (n / 2 + 1)).sum fun k =>
    let c_k := n.choose k
    let c_k_prev := if k = 0 then 0 else n.choose (k - 1)
    (c_k - c_k_prev) ^ 3
  let denominator := n.choose (n / 2)
  numerator / denominator

def A003162.b (n : ℕ) : ℕ :=
  A003162 (2 * n - 1)

def check_val (n k p : ℕ) : Bool :=
  let lhs : ℤ := A003162.b (n * p ^ k)
  let rhs : ℤ := A003162.b (n * p ^ (k - 1))
  let m : ℤ := (p : ℤ) ^ (3 * k)
  lhs ≡ rhs [ZMOD m]

#eval! check_val 1 1 5
#eval! check_val 2 1 5
#eval! check_val 1 2 5
#eval! check_val 2 2 5
