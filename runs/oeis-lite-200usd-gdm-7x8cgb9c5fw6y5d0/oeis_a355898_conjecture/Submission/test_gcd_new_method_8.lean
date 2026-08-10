import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 200000

open Nat

-- We mock A355898_loop here to make it compile, but we'll use the real one in Spec.lean.
def A355898_loop : ℕ → ℕ → ℕ → ℕ × ℕ
| 0, a, b => (a, b)
| n + 1, a, b => (b, a)

def B0 : ℕ := (A355898_loop 3772 1 1).1 + 1
def B1 : ℕ := (A355898_loop 3772 1 1).2 + 1

def B : ℕ → ℕ
| 0 => B0
| 1 => B1
| k + 2 => B (k + 1) + B k

lemma B_gcd_div_fib_sub_1 (k : ℕ) (d : ℕ) (hd_Bkp1_sub_1 : (d : ℤ) ∣ (B (k+1) : ℤ) - 1) (hd_Bk_sub_1 : (d : ℤ) ∣ (B k : ℤ) - 1) (j : ℕ) (hj_pos : 1 ≤ j) (hj : j ≤ k) :
  (d : ℤ) ∣ (B (k - j) : ℤ) - (-1 : ℤ)^j * (Nat.fib (j - 1) : ℤ) := sorry

lemma fib_identity_reduction (k : ℕ) (hk : 2 ≤ k) :
  (Nat.fib (k - 2) : ℤ) * (Nat.fib (k + 1) : ℤ) - (Nat.fib (k - 1) : ℤ) * (Nat.fib k : ℤ) =
  (Nat.fib (k - 2) : ℤ) * (Nat.fib k : ℤ) - (Nat.fib (k - 1) : ℤ)^2 := sorry

lemma fib_identity_proven (k : ℕ) (hk : 2 ≤ k) :
  (Nat.fib (k - 2) : ℤ) * (Nat.fib (k + 1) : ℤ) - (Nat.fib (k - 1) : ℤ) * (Nat.fib k : ℤ) = (-1 : ℤ)^(k - 1) := by sorry

def C_val : ℕ := B 1^2 - B 2 * B 0

theorem B_le : B 2 * B 0 ≤ B 1^2 := sorry

lemma B_gcd_div_C_val (k : ℕ) (hk : 2 ≤ k) (d : ℕ) (hd1_z : (d : ℤ) ∣ (B (k + 1) : ℤ) - 1) (hd2_z : (d : ℤ) ∣ (B k : ℤ) - 1) :
  (d : ℤ) ∣ (C_val : ℤ) + (-1 : ℤ)^k := by
  have h_div_k := B_gcd_div_fib_sub_1 k d hd1_z hd2_z k (by omega) (by omega)
  have h_div_km1 := B_gcd_div_fib_sub_1 k d hd1_z hd2_z (k - 1) (by omega) (by omega)
  have h_sub_k : k - k = 0 := by omega
  have h_sub_km1 : k - (k - 1) = 1 := by omega
  rw [h_sub_k] at h_div_k
  rw [h_sub_km1] at h_div_km1
  have h_idx_sub : k - 1 - 1 = k - 2 := by omega
  rw [h_idx_sub] at h_div_km1
  obtain ⟨q_k, hq_k⟩ := h_div_k
  obtain ⟨q_km1, hq_km1⟩ := h_div_km1
  have hB0_z : (B 0 : ℤ) = d * q_k + (-1 : ℤ)^k * (Nat.fib (k - 1) : ℤ) := by omega
  have hB1_z : (B 1 : ℤ) = d * q_km1 + (-1 : ℤ)^(k - 1) * (Nat.fib (k - 2) : ℤ) := by omega
  
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
  have h_alg : (d * q_km1 + (-1 : ℤ)^(k - 1) * F_km2)^2 - ((d * q_km1 + (-1 : ℤ)^(k - 1) * F_km2) + (d * q_k + (-1 : ℤ)^k * F_km1)) * (d * q_k + (-1 : ℤ)^k * F_km1) + (-1 : ℤ)^k =
    d * (q_km1^2 * d + 2 * q_km1 * (-1 : ℤ)^(k - 1) * F_km2 - q_km1 * q_k * d - q_km1 * (-1 : ℤ)^k * F_km1 - q_k * (-1 : ℤ)^(k - 1) * F_km2 - q_k^2 * d - 2 * q_k * (-1 : ℤ)^k * F_km1) +
    ((-1 : ℤ)^(k - 1) * (-1 : ℤ)^(k - 1)) * (F_km2^2 + F_km2 * F_km1 - F_km1^2) + (-1 : ℤ)^k := by
    rw [h_pow]
    ring
  rw [h_alg, h_P_sq]
  have h_finish : (1 : ℤ) * (F_km2^2 + F_km2 * F_km1 - F_km1^2) + (-1 : ℤ)^k = 0 := by
    rw [h_pow]
    linarith [h_fib_expand]
  have h_alg_finish : d * (q_km1^2 * d + 2 * q_km1 * (-1 : ℤ)^(k - 1) * F_km2 - q_km1 * q_k * d - q_km1 * (-1 : ℤ)^k * F_km1 - q_k * (-1 : ℤ)^(k - 1) * F_km2 - q_k^2 * d - 2 * q_k * (-1 : ℤ)^k * F_km1) + (1 * (F_km2^2 + F_km2 * F_km1 - F_km1^2) + (-1 : ℤ)^k) =
    d * (q_km1^2 * d + 2 * q_km1 * (-1 : ℤ)^(k - 1) * F_km2 - q_km1 * q_k * d - q_km1 * (-1 : ℤ)^k * F_km1 - q_k * (-1 : ℤ)^(k - 1) * F_km2 - q_k^2 * d - 2 * q_k * (-1 : ℤ)^k * F_km1) := by
    linarith [h_finish]
  rw [h_alg_finish]
  exact dvd_mul_right _ _
