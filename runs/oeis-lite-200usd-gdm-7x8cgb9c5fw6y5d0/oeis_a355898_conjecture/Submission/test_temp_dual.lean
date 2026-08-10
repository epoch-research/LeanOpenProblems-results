import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Linarith

set_option maxRecDepth 200000

open Nat

-- Mock A355898_loop
def A355898_loop : ℕ → ℕ → ℕ → ℕ × ℕ
| 0, a, b => (a, b)
| n + 1, a, b => (b, a)

def B0 : ℕ := (A355898_loop 3772 1 1).1 + 1
def B1 : ℕ := (A355898_loop 3772 1 1).2 + 1

def B : ℕ → ℕ
| 0 => B0
| 1 => B1
| k + 2 => B (k + 1) + B k

theorem B_pos (m : ℕ) : 1 ≤ B m := by
  induction m with
  | zero => simp [B, B0]
  | succ m ih =>
    cases m with
    | zero => simp [B, B1]
    | succ m =>
      have h_rec : B (m + 2) = B (m + 1) + B m := rfl
      rw [h_rec]
      omega

lemma B_gcd_div_fib_dual (k : ℕ) (d : ℕ) (hd_Bkp1_sub_1 : (d : ℤ) ∣ (B (k+1) : ℤ) - 1) (hd_Bk : (d : ℤ) ∣ (B k : ℤ)) (j : ℕ) (hj : j ≤ k) :
  (d : ℤ) ∣ (B (k - j) : ℤ) + (-1 : ℤ)^j * (Nat.fib j : ℤ) := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    rcases j with _ | j
    · simp [B]
      exact hd_Bk
    · rcases j with _ | j
      · have h_rec : B (k + 1) = B k + B (k - 1) := by
          have hk : k ≥ 1 := by omega
          obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
          subst hm
          rfl
        have h_rec_z : (B (k + 1) : ℤ) = (B k : ℤ) + (B (k - 1) : ℤ) := by exact_mod_cast h_rec
        have h_sub_1 : (B (k - 1) : ℤ) - 1 = ((B (k + 1) : ℤ) - 1) - (B k : ℤ) := by omega
        have hd_sub_1 : (d : ℤ) ∣ (B (k - 1) : ℤ) - 1 := by
          rw [h_sub_1]
          exact dvd_sub hd_Bkp1_sub_1 hd_Bk
        exact hd_sub_1
      · have ih1 := ih j (by omega) (by omega)
        have ih2 := ih (j + 1) (by omega) (by omega)
        have h_idx2 : k - (j + 1) = k - 1 - j := by omega
        rw [h_idx2] at ih2
        have h_rec_B : B (k - j) = B (k - 1 - j) + B (k - 2 - j) := by
          have h1 : k - j = (k - 2 - j) + 2 := by omega
          have h2 : k - 1 - j = (k - 2 - j) + 1 := by omega
          rw [h1, h2]
          rfl
        have h_rec_B_z : (B (k - j) : ℤ) = (B (k - 1 - j) : ℤ) + (B (k - 2 - j) : ℤ) := by exact_mod_cast h_rec_B
        have h_fib : Nat.fib (j + 2) = Nat.fib j + Nat.fib (j + 1) := Nat.fib_add_two
        have h_fib_z : (Nat.fib (j + 2) : ℤ) = (Nat.fib j : ℤ) + (Nat.fib (j + 1) : ℤ) := by exact_mod_cast h_fib
        have h_comb : (B (k - 2 - j) : ℤ) + (-1 : ℤ)^(j + 2) * (Nat.fib (j + 2) : ℤ) =
          ((B (k - j) : ℤ) + (-1 : ℤ)^j * (Nat.fib j : ℤ)) -
          ((B (k - 1 - j) : ℤ) + (-1 : ℤ)^(j + 1) * (Nat.fib (j + 1) : ℤ)) := by
          have h_pow1 : (-1 : ℤ)^(j + 2) = (-1 : ℤ)^j := by rw [pow_add, pow_two]; ring
          have h_pow2 : (-1 : ℤ)^(j + 1) = -(-1 : ℤ)^j := by rw [pow_add, pow_one]; ring
          rw [h_rec_B_z, h_fib_z, h_pow1, h_pow2]
          ring
        have h_index : k - (j + 2) = k - 2 - j := by omega
        rw [h_index]
        have h_goal_pow : (-1 : ℤ)^(j + 1 + 1) = (-1 : ℤ)^(j + 2) := rfl
        have h_goal_fib : (Nat.fib (j + 1 + 1) : ℤ) = (Nat.fib (j + 2) : ℤ) := rfl
        rw [h_goal_pow, h_goal_fib]
        rw [h_comb]
        exact dvd_sub ih1 ih2


lemma fib_identity_reduction (k : ℕ) (hk : 2 ≤ k) :
  (Nat.fib (k - 2) : ℤ) * (Nat.fib (k + 1) : ℤ) - (Nat.fib (k - 1) : ℤ) * (Nat.fib k : ℤ) =
  (Nat.fib (k - 2) : ℤ) * (Nat.fib k : ℤ) - (Nat.fib (k - 1) : ℤ)^2 := by
  have h_rec : Nat.fib (k + 1) = Nat.fib k + Nat.fib (k - 1) := by
    have h1 : k + 1 = (k - 1) + 2 := by omega
    nth_rw 1 [h1]
    rw [Nat.fib_add_two]
    have h3 : k - 1 + 1 = k := by omega
    rw [h3]
    rw [add_comm]
  have h_rec_z : (Nat.fib (k + 1) : ℤ) = (Nat.fib k : ℤ) + (Nat.fib (k - 1) : ℤ) := by exact_mod_cast h_rec
  have h_rec2 : Nat.fib k = Nat.fib (k - 1) + Nat.fib (k - 2) := by
    have h1 : k = (k - 2) + 2 := by omega
    nth_rw 1 [h1]
    rw [Nat.fib_add_two]
    have h3 : k - 2 + 1 = k - 1 := by omega
    rw [h3]
    rw [add_comm]
  have h_rec2_z : (Nat.fib k : ℤ) = (Nat.fib (k - 1) : ℤ) + (Nat.fib (k - 2) : ℤ) := by exact_mod_cast h_rec2
  rw [h_rec_z, h_rec2_z]
  ring

lemma fib_identity_proven (k : ℕ) (hk : 2 ≤ k) :
  (Nat.fib (k - 2) : ℤ) * (Nat.fib (k + 1) : ℤ) - (Nat.fib (k - 1) : ℤ) * (Nat.fib k : ℤ) = (-1 : ℤ)^(k - 1) := by
  have h_red := fib_identity_reduction k hk
  rw [h_red]
  have h_cass := fib_Cassini (k - 2)
  by_cases h_even : Even (k - 2)
  · have h_even_val := h_cass.1 h_even
    have h_idx1 : k - 2 + 1 = k - 1 := by omega
    have h_idx2 : k - 2 + 2 = k := by omega
    rw [h_idx1, h_idx2] at h_even_val
    have h_even_val_z : (Nat.fib (k - 1) : ℤ)^2 = (Nat.fib k : ℤ) * (Nat.fib (k - 2) : ℤ) + 1 := by exact_mod_cast h_even_val
    have h_pow : (-1 : ℤ)^(k - 1) = -1 := by
      rcases h_even with ⟨r, hr⟩
      have hk_val : k - 1 = 2 * r + 1 := by omega
      rw [hk_val]
      rw [pow_add, pow_one, pow_mul]
      ring
    rw [h_pow]
    linarith
  · have h_odd : Odd (k - 2) := (Nat.even_or_odd (k - 2)).resolve_left h_even
    have h_odd_val := h_cass.2 h_odd
    have h_idx1 : k - 2 + 1 = k - 1 := by omega
    have h_idx2 : k - 2 + 2 = k := by omega
    rw [h_idx1, h_idx2] at h_odd_val
    have h_odd_val_z : (Nat.fib k : ℤ) * (Nat.fib (k - 2) : ℤ) = (Nat.fib (k - 1) : ℤ)^2 + 1 := by exact_mod_cast h_odd_val
    have h_pow : (-1 : ℤ)^(k - 1) = 1 := by
      rcases h_odd with ⟨r, hr⟩
      have hk_val : k - 1 = 2 * (r + 1) := by omega
      rw [hk_val]
      rw [pow_mul]
      ring
    rw [h_pow]
    linarith

def C_val : ℕ := B 1^2 - B 2 * B 0

theorem B_le : B 2 * B 0 ≤ B 1^2 := by
  have h_B2 : B 2 = B 1 + B 0 := rfl
  have h_B1 : B 1 = B1 := rfl
  have h_B0 : B 0 = B0 := rfl
  rw [h_B2, h_B1, h_B0]
  unfold B1 B0
  decide

lemma B_gcd_div_C_val_dual (k : ℕ) (hk : 2 ≤ k) (d : ℕ) (hd1_z : (d : ℤ) ∣ (B (k + 1) : ℤ) - 1) (hd2_z : (d : ℤ) ∣ (B k : ℤ)) :
  (d : ℤ) ∣ (C_val : ℤ) - (-1 : ℤ)^k := by
  have h_div_k := B_gcd_div_fib_dual k d hd1_z hd2_z k (by omega)
  have h_div_km1 := B_gcd_div_fib_dual k d hd1_z hd2_z (k - 1) (by omega)
  have h_sub_k : k - k = 0 := by omega
  have h_sub_km1 : k - (k - 1) = 1 := by omega
  rw [h_sub_k] at h_div_k
  rw [h_sub_km1] at h_div_km1
  obtain ⟨q_k, hq_k⟩ := h_div_k
  obtain ⟨q_km1, hq_km1⟩ := h_div_km1
  have hB0_z : (B 0 : ℤ) = d * q_k - (-1 : ℤ)^k * (Nat.fib k : ℤ) := by omega
  have hB1_z : (B 1 : ℤ) = d * q_km1 - (-1 : ℤ)^(k - 1) * (Nat.fib (k - 1) : ℤ) := by omega

  set F_k := (Nat.fib k : ℤ)
  set F_km1 := (Nat.fib (k - 1) : ℤ)
  set F_km2 := (Nat.fib (k - 2) : ℤ)

  have h_fib_id : (Nat.fib (k - 2) : ℤ) * (Nat.fib k : ℤ) - (Nat.fib (k - 1) : ℤ)^2 = (-1 : ℤ)^(k - 1) := by
    rw [← fib_identity_reduction k hk, fib_identity_proven k hk]
  have h_fib_rec : (Nat.fib k : ℤ) = (Nat.fib (k - 1) : ℤ) + (Nat.fib (k - 2) : ℤ) := by
    have h1 : k = (k - 2) + 2 := by omega
    nth_rw 1 [h1]
    rw [Nat.fib_add_two]
    have h3 : k - 2 + 1 = k - 1 := by omega
    rw [h3]
    push_cast
    ring
  have h_fib_expand : F_km1^2 - F_km1 * F_km2 - F_km2^2 = - (-1 : ℤ)^(k - 1) := by
    have : F_km1^2 - F_km1 * F_km2 - F_km2^2 = - ((Nat.fib (k - 2) : ℤ) * (Nat.fib k : ℤ) - (Nat.fib (k - 1) : ℤ)^2) := by
      rw [h_fib_rec]
      ring
    rw [this, h_fib_id]

  have h_pow : (-1 : ℤ)^k = - (-1 : ℤ)^(k - 1) := by
    have : k = (k - 1) + 1 := by omega
    nth_rw 1 [this]
    rw [pow_add, pow_one]
    ring

  have h_C_val : (C_val : ℤ) = (B 1 : ℤ)^2 - ((B 1 : ℤ) + (B 0 : ℤ)) * (B 0 : ℤ) := by
    have h_C : C_val = B 1^2 - B 2 * B 0 := rfl
    have h_le : B 2 * B 0 ≤ B 1^2 := B_le
    rw [h_C]
    rw [Nat.cast_sub h_le]
    push_cast
    have h_rec : B 2 = B 1 + B 0 := rfl
    rw [h_rec]
    push_cast
    ring

  rw [h_C_val, hB0_z, hB1_z]
  have h_P_sq : (-1 : ℤ)^(k - 1) * (-1 : ℤ)^(k - 1) = 1 := by
    rw [← pow_two]
    have : (-1 : ℤ)^2 = 1 := rfl
    rw [← pow_mul, mul_comm, pow_mul, this, one_pow]
  have h_F_k : F_k = F_km1 + F_km2 := h_fib_rec
  have h_alg : (d * q_km1 - (-1 : ℤ)^(k - 1) * F_km1)^2 - ((d * q_km1 - (-1 : ℤ)^(k - 1) * F_km1) + (d * q_k - (-1 : ℤ)^k * F_k)) * (d * q_k - (-1 : ℤ)^k * F_k) - (-1 : ℤ)^k =
    d * (q_km1^2 * d - 2 * q_km1 * (-1 : ℤ)^(k - 1) * F_km1 - q_km1 * q_k * d + q_km1 * (-1 : ℤ)^k * F_k + q_k * (-1 : ℤ)^(k - 1) * F_km1 - q_k^2 * d + 2 * q_k * (-1 : ℤ)^k * F_k) +
    ((-1 : ℤ)^(k - 1) * (-1 : ℤ)^(k - 1)) * (F_km1^2 + F_km1 * F_k - F_k^2) - (-1 : ℤ)^k := by
    rw [h_pow]
    ring
  rw [h_alg, h_P_sq]
  have h_finish : (1 : ℤ) * (F_km1^2 + F_km1 * F_k - F_k^2) - (-1 : ℤ)^k = 0 := by
    rw [h_pow, h_F_k]
    linarith [h_fib_expand]
  have h_goal_eq : d * (q_km1^2 * d - 2 * q_km1 * (-1 : ℤ)^(k - 1) * F_km1 - q_km1 * q_k * d + q_km1 * (-1 : ℤ)^k * F_k + q_k * (-1 : ℤ)^(k - 1) * F_km1 - q_k^2 * d + 2 * q_k * (-1 : ℤ)^k * F_k) + 1 * (F_km1^2 + F_km1 * F_k - F_k^2) - (-1 : ℤ)^k = d * (q_km1^2 * d - 2 * q_km1 * (-1 : ℤ)^(k - 1) * F_km1 - q_km1 * q_k * d + q_km1 * (-1 : ℤ)^k * F_k + q_k * (-1 : ℤ)^(k - 1) * F_km1 - q_k^2 * d + 2 * q_k * (-1 : ℤ)^k * F_k) := by
    linarith [h_finish]
  rw [h_goal_eq]
  exact dvd_mul_right _ _
