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

def a_Q_rec (n : ℕ) : ℚ :=
  match n with
  | 0 => 0
  | 1 => 2
  | k + 2 =>
    let n_idx := k + 2
    let n_q : ℚ := n_idx
    let a_prev : ℚ := a_Q_rec (n_idx - 1)
    let term1 : ℚ := 32 * n_q ^ 3 * a_prev
    let P_n : ℚ := 21 * n_q ^ 3 + 22 * n_q ^ 2 + 8 * n_q + 1
    let binom_pow4 : ℚ := (Nat.choose (2 * n_idx - 1) n_idx : ℚ) ^ 4
    let numerator : ℚ := term1 + P_n * binom_pow4
    let denominator : ℚ := (2 * n_q + 1) ^ 3
    numerator / denominator

noncomputable def a_Q (n : ℕ) : ℚ :=
  match n with
  | 0 => 0
  | 1 => 2
  | k + 2 =>
    let n_idx := k + 2
    let n_q : ℚ := n_idx
    let a_prev : ℚ := a_Q (n_idx - 1)
    let term1 : ℚ := 32 * n_q ^ 3 * a_prev
    let P_n : ℚ := 21 * n_q ^ 3 + 22 * n_q ^ 2 + 8 * n_q + 1
    let binom_pow4 : ℚ := (Nat.choose (2 * n_idx - 1) n_idx : ℚ) ^ 4
    let numerator : ℚ := term1 + P_n * binom_pow4
    let denominator : ℚ := (2 * n_q + 1) ^ 3
    numerator / denominator

lemma a_Q_eq_div (n : ℕ) : a_Q n = (num n : ℚ) / (den n : ℚ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _|n
    · unfold a_Q num den
      norm_num
    rcases n with _|k
    · unfold a_Q num den
      norm_num
    · have h1 : k + 1 < k + 2 := Nat.lt_succ_self (k + 1)
      have ih1 := ih (k + 1) h1
      unfold a_Q
      dsimp only
      have h_sub : k + 2 - 1 = k + 1 := rfl
      rw [h_sub]
      rw [ih1]
      have h_num : num (k + 2) = 32 * (k + 2) ^ 3 * num (k + 1) + (21 * (k + 2) ^ 3 + 22 * (k + 2) ^ 2 + 8 * (k + 2) + 1) * (Nat.choose (2 * (k + 2) - 1) (k + 2)) ^ 4 * den (k + 1) := rfl
      have h_den : den (k + 2) = (2 * (k + 2) + 1) ^ 3 * den (k + 1) := rfl
      rw [h_num, h_den]
      push_cast
      have h_den_pos : (den (k + 1) : ℚ) ≠ 0 := by
        have := den_pos (k + 1)
        positivity
      have h_den2 : (2 * (k + 2 : ℚ) + 1) ^ 3 ≠ 0 := by positivity
      field_simp

lemma poly_identity (n : ℤ) :
  (21 * (n+1) ^ 3 + 22 * (n+1) ^ 2 + 8 * (n+1) + 1) - (n+1) ^ 3 * (4 * n + 5) ^ 2 =
  (-2 * n ^ 2 - 2 * n + 1) * (2 * n + 3) ^ 3 := by ring

-- Let's define the induction hypothesis
def IndHyp (n : ℕ) : Prop :=
  (∃ (k : ℕ), a_Q n = (k : ℚ)) ∧
  (∃ (K : ℤ), 32 * ((num n / den n : ℕ) : ℤ) + (4 * (n : ℤ) + 5) ^ 2 * (Nat.choose (2 * n + 1) (n + 1) : ℤ) ^ 4 = (2 * (n : ℤ) + 3) ^ 3 * K)


lemma den_step (n : ℕ) (hn : n ≥ 1) : den (n + 1) = (2 * n + 3) ^ 3 * den n := by
  rcases n with _|k
  · contradiction
  · rfl

lemma num_step (n : ℕ) (hn : n ≥ 1) :
    num (n + 1) = 32 * (n + 1) ^ 3 * num n + (21 * (n + 1) ^ 3 + 22 * (n + 1) ^ 2 + 8 * (n + 1) + 1) * (Nat.choose (2 * n + 1) (n + 1)) ^ 4 * den n := by
  rcases n with _|k
  · contradiction
  · have h_choose : 2 * (k + 2) - 1 = 2 * (k + 1) + 1 := by omega
    have h_num : num (k + 2) = 32 * (k + 2) ^ 3 * num (k + 1) + (21 * (k + 2) ^ 3 + 22 * (k + 2) ^ 2 + 8 * (k + 2) + 1) * (Nat.choose (2 * (k + 2) - 1) (k + 2)) ^ 4 * den (k + 1) := rfl
    rw [h_num, h_choose]


lemma ind_hyp_one : IndHyp 1 := by
  constructor
  · use 2
    unfold a_Q
    norm_num
  · use 53
    have h1 : num 1 / den 1 = 2 := by decide
    rw [h1]
    decide


lemma ind_hyp_step (n : ℕ) (hn : n ≥ 1) (ih : IndHyp n) : IndHyp (n + 1) := by
  rcases ih with ⟨⟨k, hk⟩, ⟨K, hK⟩⟩
  have h_num_eq : num n = k * den n := by
    have h_div := a_Q_eq_div n
    rw [hk] at h_div
    have h_den_pos : (den n : ℚ) ≠ 0 := by
      have := den_pos n
      positivity
    have h_mul := (div_eq_iff h_den_pos).mp h_div.symm
    push_cast at h_mul
    exact_mod_cast h_mul
  have h_nat_div : num n / den n = k := by
    rw [h_num_eq]
    exact Nat.mul_div_cancel k (den_pos n)
  have hK_k : 32 * (k : ℤ) + (4 * (n : ℤ) + 5) ^ 2 * (Nat.choose (2 * n + 1) (n + 1) : ℤ) ^ 4 = (2 * (n : ℤ) + 3) ^ 3 * K := by
    rw [h_nat_div] at hK
    exact hK
  let Q_val : ℤ := (n + 1 : ℤ) ^ 3 * K + (-2 * (n : ℤ) ^ 2 - 2 * (n : ℤ) + 1) * (Nat.choose (2 * n + 1) (n + 1) : ℤ) ^ 4
  have h_num_next_eq : (num (n + 1) : ℤ) = ((2 * n + 3 : ℤ) ^ 3 * Q_val) * (den n : ℤ) := by
    rw [num_step n hn]
    rw [h_num_eq]
    push_cast
    have h_poly : 32 * (n + 1 : ℤ) ^ 3 * ((k : ℤ) * (den n : ℤ)) + (21 * (n + 1 : ℤ) ^ 3 + 22 * (n + 1 : ℤ) ^ 2 + 8 * (n + 1 : ℤ) + 1) * (Nat.choose (2 * n + 1) (n + 1) : ℤ) ^ 4 * (den n : ℤ) =
                  (32 * (n + 1 : ℤ) ^ 3 * (k : ℤ) + (21 * (n + 1 : ℤ) ^ 3 + 22 * (n + 1 : ℤ) ^ 2 + 8 * (n + 1 : ℤ) + 1) * (Nat.choose (2 * n + 1) (n + 1) : ℤ) ^ 4) * (den n : ℤ) := by ring
    rw [h_poly]
    have h_K_sub : 32 * (k : ℤ) = (2 * (n : ℤ) + 3) ^ 3 * K - (4 * (n : ℤ) + 5) ^ 2 * (Nat.choose (2 * n + 1) (n + 1) : ℤ) ^ 4 := by omega
    have h_poly2 : 32 * (n + 1 : ℤ) ^ 3 * (k : ℤ) = (n + 1 : ℤ) ^ 3 * (32 * (k : ℤ)) := by ring
    rw [h_poly2, h_K_sub]
    have h_poly_final : ((n + 1 : ℤ) ^ 3 * ((2 * (n : ℤ) + 3) ^ 3 * K - (4 * (n : ℤ) + 5) ^ 2 * (Nat.choose (2 * n + 1) (n + 1) : ℤ) ^ 4) +
                        (21 * (n + 1 : ℤ) ^ 3 + 22 * (n + 1 : ℤ) ^ 2 + 8 * (n + 1 : ℤ) + 1) * (Nat.choose (2 * n + 1) (n + 1) : ℤ) ^ 4) =
                       (2 * n + 3 : ℤ) ^ 3 * Q_val := by
      have h_poly_identity := poly_identity (n : ℤ)
      have h_comm : (-2 * (n : ℤ) ^ 2 - 2 * (n : ℤ) + 1) * (2 * n + 3 : ℤ) ^ 3 = (2 * n + 3 : ℤ) ^ 3 * (-2 * (n : ℤ) ^ 2 - 2 * (n : ℤ) + 1) := by ring
      rw [h_comm] at h_poly_identity
      dsimp [Q_val]
      have h_expand : (2 * n + 3 : ℤ) ^ 3 * ((n + 1 : ℤ) ^ 3 * K + (-2 * (n : ℤ) ^ 2 - 2 * (n : ℤ) + 1) * (Nat.choose (2 * n + 1) (n + 1) : ℤ) ^ 4) =
                      (n + 1 : ℤ) ^ 3 * ((2 * n + 3 : ℤ) ^ 3 * K) + ((2 * n + 3 : ℤ) ^ 3 * (-2 * (n : ℤ) ^ 2 - 2 * (n : ℤ) + 1)) * (Nat.choose (2 * n + 1) (n + 1) : ℤ) ^ 4 := by ring
      rw [h_expand]
      rw [← h_poly_identity]
      rw [← hK_k]
      ring
    rw [h_poly_final]
  fail
