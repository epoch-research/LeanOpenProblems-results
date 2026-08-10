import FormalConjectures.Util.ProblemImports

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

noncomputable def a_Q (n : ℕ) : ℚ := (num n : ℚ) / (den n : ℚ)
noncomputable def a (n : ℕ) : ℕ := (a_Q n).floor.toNat

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

lemma rat_floor_div_eq_nat_div (A B : ℕ) (hB : B > 0) :
    (((A : ℚ) / (B : ℚ)).floor) = ↑(A / B : ℕ) := by
  have h_eq : ((A : ℚ) / (B : ℚ)).floor = ↑(A / B : ℕ) ↔ ↑(A / B : ℕ) ≤ ((A : ℚ) / (B : ℚ)).floor ∧ ((A : ℚ) / (B : ℚ)).floor < ↑(A / B : ℕ) + 1 := by
    constructor
    · intro h
      rw [h]
      constructor <;> omega
    · rintro ⟨h1, h2⟩
      omega
  rw [h_eq]
  constructor
  · rw [Rat.le_floor_iff]
    rw [le_div_iff₀]
    · have h_div : A / B * B ≤ A := Nat.div_mul_le_self A B
      exact_mod_cast h_div
    · positivity
  · rw [Rat.floor_lt_iff]
    rw [div_lt_iff₀]
    · push_cast
      have h_div : A < B * (A / B) + B := by
        have h_div_mod := Nat.div_add_mod A B
        have h_mod := Nat.mod_lt A hB
        nth_rw 1 [← h_div_mod]
        omega
      have h_div_q : (A : ℚ) < ↑(B * (A / B) + B) := by exact_mod_cast h_div
      have h_ring : ((B * (A / B) + B : ℕ) : ℚ) = (↑(A / B) + 1) * ↑B := by
        push_cast
        ring
      rw [h_ring] at h_div_q
      exact h_div_q
    · positivity

lemma a_eq_nat_div (n : ℕ) : a n = num n / den n := by
  unfold a a_Q
  rw [rat_floor_div_eq_nat_div (num n) (den n) (den_pos n)]
  rfl

lemma dvd_of_mod_mul_eq (N D C : ℕ) (h : N % (2 * D) = (C * D) % (2 * D)) : D ∣ N := by
  have h1 : N % (2 * D) % D = ((C * D) % (2 * D)) % D := by rw [h]
  rw [Nat.mod_mul_left_mod N 2 D, Nat.mod_mul_left_mod (C * D) 2 D] at h1
  have h_cd : (C * D) % D = 0 := Nat.mul_mod_left C D
  rw [h_cd] at h1
  exact Nat.dvd_of_mod_eq_zero h1

lemma test_induction_step (k : ℕ)
    (h_ih : num (k + 1) % (2 * den (k + 1)) = (Nat.choose k ((k + 1) / 2) * den (k + 1)) % (2 * den (k + 1))) :
    num (k + 1) = a (k + 1) * den (k + 1) := by
  have h_dvd : den (k + 1) ∣ num (k + 1) := dvd_of_mod_mul_eq (num (k + 1)) (den (k + 1)) (Nat.choose k ((k + 1) / 2)) h_ih
  rw [a_eq_nat_div]
  exact (Nat.div_mul_cancel h_dvd).symm
