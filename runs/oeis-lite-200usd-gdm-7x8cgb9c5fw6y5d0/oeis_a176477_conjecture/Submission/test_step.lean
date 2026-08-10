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

lemma dvd_of_mod_mul_eq (N D C : ℕ) (h : N % (2 * D) = (C * D) % (2 * D)) : D ∣ N := by
  have h1 : N % (2 * D) % D = ((C * D) % (2 * D)) % D := by rw [h]
  rw [Nat.mod_mul_left_mod N 2 D, Nat.mod_mul_left_mod (C * D) 2 D] at h1
  have h_cd : (C * D) % D = 0 := Nat.mul_mod_left C D
  rw [h_cd] at h1
  exact Nat.dvd_of_mod_eq_zero h1

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
    · -- n = 2
      rfl
    rcases k with _|k
    · -- n = 3
      rfl
    · -- n = k + 4
      have ih_k3 := ih (k + 3) (by omega) (by omega)
      have h_dvd : den (k + 3) ∣ num (k + 3) := dvd_of_mod_mul_eq (num (k + 3)) (den (k + 3)) (choose (k + 2) ((k + 3) / 2)) ih_k3
      have h_eq : num (k + 3) = (num (k + 3) / den (k + 3)) * den (k + 3) := (Nat.div_mul_cancel h_dvd).symm
      have h_num : num (k + 4) = 32 * (k + 4) ^ 3 * num (k + 3) + (21 * (k + 4) ^ 3 + 22 * (k + 4) ^ 2 + 8 * (k + 4) + 1) * (Nat.choose (2 * (k + 4) - 1) (k + 4)) ^ 4 * den (k + 3) := rfl
      have h_den : den (k + 4) = (2 * (k + 4) + 1) ^ 3 * den (k + 3) := rfl
      let a_val := num (k + 3) / den (k + 3)
      let M := (2 * (k + 4) + 1) ^ 3
      have h_rhs : (k + 3).choose ((k + 4) / 2) * ((2 * (k + 4) + 1) ^ 3 * den (k + 3)) = ((k + 3).choose ((k + 4) / 2) * (2 * (k + 4) + 1) ^ 3) * den (k + 3) := by ring
      have h_mod_lhs : 2 * ((2 * (k + 4) + 1) ^ 3 * den (k + 3)) = (2 * (2 * (k + 4) + 1) ^ 3) * den (k + 3) := by ring
      rw [h_num, h_den, h_eq]
      change
        (32 * (k + 4) ^ 3 * (num (k + 3) / den (k + 3) * den (k + 3)) +
         (21 * (k + 4) ^ 3 + 22 * (k + 4) ^ 2 + 8 * (k + 4) + 1) * (2 * (k + 4) - 1).choose (k + 4) ^ 4 * den (k + 3)) %
        (2 * ((2 * (k + 4) + 1) ^ 3 * den (k + 3))) =
        (k + 3).choose ((k + 4) / 2) * ((2 * (k + 4) + 1) ^ 3 * den (k + 3)) %
        (2 * ((2 * (k + 4) + 1) ^ 3 * den (k + 3)))
      have h_lhs_ring : (32 * (k + 4) ^ 3 * (num (k + 3) / den (k + 3) * den (k + 3)) + (21 * (k + 4) ^ 3 + 22 * (k + 4) ^ 2 + 8 * (k + 4) + 1) * (2 * (k + 4) - 1).choose (k + 4) ^ 4 * den (k + 3)) = (32 * (k + 4) ^ 3 * (num (k + 3) / den (k + 3)) + (21 * (k + 4) ^ 3 + 22 * (k + 4) ^ 2 + 8 * (k + 4) + 1) * (2 * (k + 4) - 1).choose (k + 4) ^ 4) * den (k + 3) := by ring
      rw [h_lhs_ring, h_rhs, h_mod_lhs]
      rw [test_mul_mod_mul_right (32 * (k + 4) ^ 3 * (num (k + 3) / den (k + 3)) + (21 * (k + 4) ^ 3 + 22 * (k + 4) ^ 2 + 8 * (k + 4) + 1) * (choose (2 * (k + 4) - 1) (k + 4)) ^ 4) (2 * (2 * (k + 4) + 1) ^ 3) (den (k + 3))]
      rw [test_mul_mod_mul_right ((k + 3).choose ((k + 4) / 2) * (2 * (k + 4) + 1) ^ 3) (2 * (2 * (k + 4) + 1) ^ 3) (den (k + 3))]
      apply congrArg (fun x => x * den (k + 3))


