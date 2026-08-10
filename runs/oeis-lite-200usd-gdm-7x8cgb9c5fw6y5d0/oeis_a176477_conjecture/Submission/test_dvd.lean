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

theorem den_dvd_num (n : ℕ) : den n ∣ num n := by
  induction n with
  | zero =>
    simp [den, num]
  | succ n ih =>
    rcases n with _|k
    · simp [den, num]
    · -- n = k + 2 case
      -- We want den (k + 2) | num (k + 2)
      have h_den : den (k + 2) = (2 * (k + 2) + 1) ^ 3 * den (k + 1) := rfl
      have h_num : num (k + 2) = 32 * (k + 2) ^ 3 * num (k + 1) + (21 * (k + 2) ^ 3 + 22 * (k + 2) ^ 2 + 8 * (k + 2) + 1) * (Nat.choose (2 * (k + 2) - 1) (k + 2)) ^ 4 * den (k + 1) := rfl
      rw [h_den, h_num]
      have ih_k1 : den (k + 1) ∣ num (k + 1) := ih
      rcases ih_k1 with ⟨q, hq⟩
      rw [hq]
      -- Rearrange the term
      have h_rearrange : 32 * (k + 2) ^ 3 * (den (k + 1) * q) + (21 * (k + 2) ^ 3 + 22 * (k + 2) ^ 2 + 8 * (k + 2) + 1) * (Nat.choose (2 * (k + 2) - 1) (k + 2)) ^ 4 * den (k + 1) =
                         (32 * (k + 2) ^ 3 * q + (21 * (k + 2) ^ 3 + 22 * (k + 2) ^ 2 + 8 * (k + 2) + 1) * (Nat.choose (2 * (k + 2) - 1) (k + 2)) ^ 4) * den (k + 1) := by ring
      rw [h_rearrange]
      have h_den_pos : den (k + 1) > 0 := den_pos (k + 1)
      -- Use dvd_mul_cancel_right or similar
      have h_dvd_iff : (2 * (k + 2) + 1) ^ 3 * den (k + 1) ∣ (32 * (k + 2) ^ 3 * q + (21 * (k + 2) ^ 3 + 22 * (k + 2) ^ 2 + 8 * (k + 2) + 1) * (Nat.choose (2 * (k + 2) - 1) (k + 2)) ^ 4) * den (k + 1) ↔
                       (2 * (k + 2) + 1) ^ 3 ∣ 32 * (k + 2) ^ 3 * q + (21 * (k + 2) ^ 3 + 22 * (k + 2) ^ 2 + 8 * (k + 2) + 1) * (Nat.choose (2 * (k + 2) - 1) (k + 2)) ^ 4 := by
        exact mul_dvd_mul_iff_right (_root_.ne_of_gt h_den_pos)
      rw [h_dvd_iff]
      sorry
