import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic

set_option exponentiation.threshold 30000000
set_option maxRecDepth 10000000

open Nat ZMod

def f_seq (M : ℕ) : ℕ → (ZMod M → ZMod M)
  | 0 => fun z => z ^ 10
  | i + 1 => fun z => f_seq M i (f_seq M i z)

theorem f_seq_eq (M : ℕ) (i : ℕ) (z : ZMod M) :
    f_seq M i z = z ^ (10 ^ (2 ^ i)) := by
  induction i generalizing z with
  | zero => rfl
  | succ i ih =>
    simp [f_seq, ih]
    rw [← pow_mul, ← pow_add, ← pow_succ]

theorem test_21_composite : f_seq (10^(2^21) + 1) 21 3 ≠ 1 := by
  decide
