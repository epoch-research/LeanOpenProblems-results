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
  if h : n = 0 then
    x % m
  else if n = 1 then
    step10 x m
  else
    have : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)
    have : n - n / 2 < n := Nat.sub_lt (Nat.pos_of_ne_zero h) (Nat.div_pos (by omega) (by decide))
    pow10Rec (n - n / 2) (pow10Rec (n / 2) x m) m
termination_by n

theorem test_fermat_witness_13 : pow10Rec 8192 3 (10 ^ 8192 + 1) ≠ 1 := by decide
