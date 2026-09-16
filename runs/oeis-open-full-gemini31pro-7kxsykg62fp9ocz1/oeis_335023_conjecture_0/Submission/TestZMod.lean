import Mathlib

set_option maxRecDepth 200000
set_option exponentiation.threshold 2000

def S_loop (fuel : ℕ) (acc : ℕ) : ℕ :=
  match fuel with
  | 0 => acc
  | k + 1 =>
    let sign : ℕ := if (k+1) % 2 == 0 then 1 else 1092
    let inv : ℕ := ((k+1)^1091) % 1093
    S_loop k ((acc + sign * inv) % 1093)

def S_val : ℕ := S_loop 1092 0

theorem S_eq_zero : S_val = 0 := by decide
