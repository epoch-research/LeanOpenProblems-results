import Mathlib

open Nat

set_option exponentiation.threshold 100000
set_option maxRecDepth 200000

def step10 (x m : ℕ) : ℕ :=
  let x2 := x * x % m
  let x4 := x2 * x2 % m
  let x8 := x4 * x4 % m
  x8 * x2 % m

def pow10Rec (n : ℕ) (x m : ℕ) : ℕ :=
  match n with
  | 0 => x % m
  | n + 1 => pow10Rec n (step10 x m) m

theorem test_fermat_witness_13 : pow10Rec 8192 3 (10 ^ 8192 + 1) ≠ 1 := by decide
