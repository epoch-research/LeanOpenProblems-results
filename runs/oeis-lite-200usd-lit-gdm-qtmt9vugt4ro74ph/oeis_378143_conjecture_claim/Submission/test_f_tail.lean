import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic

set_option exponentiation.threshold 30000000
set_option maxRecDepth 10000000

def f_tail (M : ℕ) : ℕ → ZMod M → ZMod M
  | 0, z => z
  | i + 1, z => f_tail M i (z ^ 10)

theorem f_tail_eq (M : ℕ) (i : ℕ) (z : ZMod M) : f_tail M i z = z ^ (10 ^ i) := by
  induction i generalizing z with
  | zero => simp [f_tail]
  | succ i ih =>
    simp [f_tail, ih]
    rw [← pow_mul]
    congr 1
    rw [mul_comm, ← pow_succ]

theorem test_13_tail : f_tail (10 ^ (2 ^ 13) + 1) (2 ^ 13) 3 ≠ 1 := by
  decide
