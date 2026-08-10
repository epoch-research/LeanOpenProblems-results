import Mathlib

open Nat

set_option exponentiation.threshold 100000
set_option maxRecDepth 200000

def step10 (x m : ℕ) : ℕ :=
  let x2 := x * x % m
  let x4 := x2 * x2 % m
  let x8 := x4 * x4 % m
  x8 * x2 % m

def pow10_2Rec (n : ℕ) (x m : ℕ) : ℕ :=
  match n with
  | 0 => step10 x m
  | n + 1 =>
    let half := pow10_2Rec n x m
    pow10_2Rec n half m

theorem test_fermat_witness_13 : pow10_2Rec 13 3 (10 ^ (2 ^ 13) + 1) ≠ 1 := by decide
