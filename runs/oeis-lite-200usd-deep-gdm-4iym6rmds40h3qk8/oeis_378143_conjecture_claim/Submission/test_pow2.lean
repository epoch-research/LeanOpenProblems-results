import Mathlib

open Nat

set_option exponentiation.threshold 100000
set_option maxRecDepth 200000

def step10 (x m : ℕ) : ℕ :=
  let x2 := x * x % m
  let x4 := x2 * x2 % m
  let x8 := x4 * x4 % m
  x8 * x2 % m

def F (m : ℕ) : ℕ → ℕ → ℕ
  | 0, y => step10 y m
  | k + 1, y => F m k (F m k y)

theorem test_fermat_witness_13 : F (10 ^ (2 ^ 13) + 1) 13 3 ≠ 1 := by decide
