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

theorem step10_eq_pow10_mod (x m : ℕ) : step10 x m = x ^ 10 % m := by
  unfold step10
  simp only [← Nat.mul_mod]
  congr 1
  ring


theorem pow10Rec_eq_pow10_mod (n : ℕ) (x m : ℕ) : pow10Rec n x m = x ^ (10 ^ n) % m := by
  induction n generalizing x with
  | zero =>
    unfold pow10Rec
    simp
  | succ n ih =>
    unfold pow10Rec
    rw [ih]
    rw [step10_eq_pow10_mod]
    rw [← Nat.pow_mod]
    rw [← Nat.pow_mul]
    have h1 : 10 * 10 ^ n = 10 ^ (n + 1) := by
      rw [Nat.pow_succ]
      ring
    rw [h1]

theorem test_fermat_witness_13 : pow10Rec 13 3 (10 ^ (2 ^ 13) + 1) ≠ 1 := by decide

theorem test_fermat_witness_14 : pow10Rec 14 3 (10 ^ (2 ^ 14) + 1) ≠ 1 := by decide


theorem test_fermat_witness_15 : pow10Rec 15 3 (10 ^ (2 ^ 15) + 1) ≠ 1 := by decide



