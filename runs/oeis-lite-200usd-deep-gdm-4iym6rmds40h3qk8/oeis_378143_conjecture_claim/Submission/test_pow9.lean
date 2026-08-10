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

def loop_256 (x m : ℕ) : ℕ :=
  pow10Rec 256 x m

def m : ℕ := 10 ^ 8192 + 1

def v0 : ℕ := 3
def v1 : ℕ := loop_256 v0 m
def v2 : ℕ := loop_256 v1 m
def v3 : ℕ := loop_256 v2 m
def v4 : ℕ := loop_256 v3 m
def v5 : ℕ := loop_256 v4 m
def v6 : ℕ := loop_256 v5 m
def v7 : ℕ := loop_256 v6 m
def v8 : ℕ := loop_256 v7 m
def v9 : ℕ := loop_256 v8 m
def v10 : ℕ := loop_256 v9 m
def v11 : ℕ := loop_256 v10 m
def v12 : ℕ := loop_256 v11 m
def v13 : ℕ := loop_256 v12 m
def v14 : ℕ := loop_256 v13 m
def v15 : ℕ := loop_256 v14 m
def v16 : ℕ := loop_256 v15 m
def v17 : ℕ := loop_256 v16 m
def v18 : ℕ := loop_256 v17 m
def v19 : ℕ := loop_256 v18 m
def v20 : ℕ := loop_256 v19 m
def v21 : ℕ := loop_256 v20 m
def v22 : ℕ := loop_256 v21 m
def v23 : ℕ := loop_256 v22 m
def v24 : ℕ := loop_256 v23 m
def v25 : ℕ := loop_256 v24 m
def v26 : ℕ := loop_256 v25 m
def v27 : ℕ := loop_256 v26 m
def v28 : ℕ := loop_256 v27 m
def v29 : ℕ := loop_256 v28 m
def v30 : ℕ := loop_256 v29 m
def v31 : ℕ := loop_256 v30 m
def v32 : ℕ := loop_256 v31 m

theorem test_fermat_witness_13 : v32 ≠ 1 := by decide
