import FormalConjectures.Util.ProblemImports

open Nat

def den : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | k + 2 => (2 * (k + 2) + 1) ^ 3 * den (k + 1)

def num : ℕ → ℕ
  | 0 => 0
  | 1 => 2
  | k + 2 =>
    let n_idx := k + 2
    let term1 := 32 * n_idx ^ 3 * num (k + 1)
    let P_n := 21 * n_idx ^ 3 + 22 * n_idx ^ 2 + 8 * n_idx + 1
    let binom_pow4 := (Nat.choose (2 * n_idx - 1) n_idx) ^ 4
    term1 + P_n * binom_pow4 * den (k + 1)

lemma den_pos (n : ℕ) : den n > 0 := by
  induction n with
  | zero => decide
  | succ n ih =>
    rcases n with _|k
    · decide
    · have : k + 2 = k + 1 + 1 := rfl
      rw [this]
      rw [den]
      positivity

lemma test_mul_mod_mul_right (a b c : ℕ) : (a * c) % (b * c) = (a % b) * c := by
  exact Nat.mul_mod_mul_right c a b

lemma num_mod_two_den_eq (n : ℕ) (hn : n ≥ 2) :
    num n % (2 * den n) = (choose (n - 1) (n / 2) * den n) % (2 * den n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _|n
    · contradiction
    rcases n with _|n
    · contradiction
    rcases n with _|k
    · -- n = 2 case
      rfl
    rcases k with _|k
    · -- n = 3 case
      rfl
    · -- n = k + 4 case
      sorry
