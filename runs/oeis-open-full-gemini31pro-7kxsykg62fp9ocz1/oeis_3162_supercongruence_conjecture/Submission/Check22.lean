import Mathlib

open Nat Finset

def A003162_num (n : ℕ) : ℕ :=
  (Finset.range (n / 2 + 1)).sum fun k =>
    let c_k := n.choose k
    let c_k_prev := if k = 0 then 0 else n.choose (k - 1)
    (c_k - c_k_prev) ^ 3

def A003162_den (n : ℕ) : ℕ := n.choose (n / 2)

def search : IO Unit := do
  for n in List.range 1000 do
    if A003162_num n % A003162_den n != 0 then
      IO.println s!"NOT EXACT: n={n}"
      return
  IO.println "Always exact."

#eval! search
