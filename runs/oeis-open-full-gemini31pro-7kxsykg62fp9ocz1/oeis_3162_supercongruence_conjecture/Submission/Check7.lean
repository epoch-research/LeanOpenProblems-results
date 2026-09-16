import Mathlib

open Nat Finset

def A003162 (n : ℕ) : ℕ :=
  let numerator := (Finset.range (n / 2 + 1)).sum fun k =>
    let c_k := n.choose k
    let c_k_prev := if k = 0 then 0 else n.choose (k - 1)
    (c_k - c_k_prev) ^ 3
  let denominator := n.choose (n / 2)
  numerator / denominator

def A003162_b (n : ℕ) : ℕ :=
  A003162 (2 * n - 1)

def check_val (n k p : ℕ) : Bool :=
  let lhs : ℤ := A003162_b (n * p ^ k)
  let rhs : ℤ := A003162_b (n * p ^ (k - 1))
  let m : ℤ := (p : ℤ) ^ (3 * k)
  lhs ≡ rhs [ZMOD m]

def search : IO Unit := do
  let primes := [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]
  for p in primes do
    for k in [1] do
      for n in List.range 10 do
        let n := n + 1
        if !check_val n k p then
          IO.println s!"COUNTEREXAMPLE: n={n}, k={k}, p={p}"
          return
  IO.println "Done."

#eval! search
