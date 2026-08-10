import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 10000

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
    rw [← pow_mul, ← pow_add, ← pow_succ]

theorem test_3 : (3 : ZMod (10^(2^3) + 1)) ^ (10^(2^3)) ≠ 1 := by
  rw [← f_seq_eq]
  decide

theorem test_13 : (3 : ZMod (10^(2^13) + 1)) ^ (10^(2^13)) ≠ 1 := by
  rw [← f_seq_eq]
  decide








