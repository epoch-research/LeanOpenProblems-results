import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic

open Nat

def f_seq (M : ℕ) : ℕ → (ZMod M → ZMod M)
  | 0 => fun z => z ^ 10
  | i + 1 => fun z => f_seq M i (f_seq M i z)

theorem f_seq_eq (M : ℕ) (i : ℕ) (z : ZMod M) :
    f_seq M i z = z ^ (10 ^ (2 ^ i)) := by
  induction i generalizing z with
  | zero =>
    simp [f_seq]
  | succ i ih =>
    simp [f_seq, ih]
    rw [← pow_mul]
    congr 1
    rw [← pow_add]
    congr 1
    omega
