import Mathlib

def blocking_prime_by_idx (idx : ℕ) : ℕ :=
  match idx with
  | 0 => 11
  | 1 => 13
  | _ => 3

lemma blocking_prime_by_idx_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx idx) := by
  unfold blocking_prime_by_idx; split <;> norm_num

lemma blocking_prime_by_idx_3mod4 (idx : ℕ) : blocking_prime_by_idx idx % 4 = 3 := by
  unfold blocking_prime_by_idx; split <;> decide
