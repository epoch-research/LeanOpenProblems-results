import Mathlib

def blocking_prime_by_idx (idx : ℕ) : ℕ :=
  match idx with
  | 0 => 11
  | _ => 3

lemma blocking_prime_by_idx_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx idx) := by
  match idx with
  | 0 =>
    dsimp [blocking_prime_by_idx]
    norm_num
  | _ =>
    dsimp [blocking_prime_by_idx]
    norm_num
