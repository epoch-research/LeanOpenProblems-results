import Mathlib

open Nat

set_option exponentiation.threshold 100000
set_option maxRecDepth 200000

def step10 (x m : ℕ) : ℕ :=
  let x2 := x * x % m
  let x4 := x2 * x2 % m
  let x8 := x4 * x4 % m
  x8 * x2 % m

def run_tree (k : ℕ) (f : ℕ → ℕ) (x : ℕ) : ℕ :=
  match k with
  | 0 => f x
  | k + 1 => run_tree k f (run_tree k f x)

theorem test_fermat_witness_13 : run_tree 13 (fun y => step10 y (10 ^ 8192 + 1)) 3 ≠ 1 := by decide
