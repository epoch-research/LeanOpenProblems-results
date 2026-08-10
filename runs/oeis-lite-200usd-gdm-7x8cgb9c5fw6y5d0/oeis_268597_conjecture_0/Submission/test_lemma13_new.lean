import FormalConjectures.Util.ProblemImports

open Nat

lemma divisor_prime_case {n : ℕ} {A d p : ℕ} (ha : A ≥ 1) (hp : Nat.Prime p) (h_cop : Nat.Coprime p A) (hd_pos : d > 0) (h_p_eq : p = d + 1) (h_A_le : A < n + 1) (h_div_d : d ∣ n + 1 - A) (h_div_phi : A.totient ∣ A - (n + 1 - A) / d) (h_ineq : A.totient * d > n) :
  ∃ x, x > 0 ∧ (x - 1) % Nat.totient x = n := by
  use A * p
  have hp_pos : p > 0 := hp.pos
  have h_x_pos : A * p > 0 := by positivity
  refine ⟨h_x_pos, ?_⟩
  have h_coprime : Nat.Coprime A p := h_cop.symm
  have h_tot : (A * p).totient = A.totient * d := by
    rw [Nat.totient_mul h_coprime]
    have h_totp := Nat.totient_prime hp
    rw [h_totp, h_p_eq]
    rfl
  rw [h_tot]
  generalize h_q : (n + 1 - A) / d = q
  have h_div_eq : d * q = n + 1 - A := by
    rw [← h_q]
    exact Nat.mul_div_cancel' h_div_d
  have h_ineq2 : A * d > q * d := by
    have h_tot_le : A.totient ≤ A := Nat.totient_le A
    have h_prod1 : A * d ≥ A.totient * d := Nat.mul_le_mul_right d h_tot_le
    have h_prod2 : A.totient * d > n + 1 - A := by
      have h_sub_lt : n + 1 - A ≤ n := by omega
      omega
    rw [← h_div_eq] at h_prod2
    have h_rw_dq : d * q = q * d := by ring
    rw [h_rw_dq] at h_prod2
    omega
  have h_A_gt_q : A > q := by
    exact Nat.lt_of_mul_lt_mul_right h_ineq2
  have h_eq : A * p - (n + 1) = (A - q) * d := by
    rw [h_p_eq]
    have h_ring : A * (d + 1) = A * d + A := by ring
    rw [h_ring]
    have h_n1 : n + 1 = A + (n + 1 - A) := by omega
    rw [h_n1, ← h_div_eq]
    have h_sub : A * d + A - (A + d * q) = A * d - d * q := by omega
    rw [h_sub]
    have h_rw_dq : d * q = q * d := by ring
    rw [h_rw_dq]
    have h_mul_sub : (A - q) * d = A * d - q * d := Nat.sub_mul A q d
    rw [h_mul_sub]
  have h_div_phi' : A.totient ∣ A - q := by
    rw [h_q] at h_div_phi
    exact h_div_phi
  rcases h_div_phi' with ⟨k, hk⟩
  have h_eq2 : A * p - (n + 1) = k * (A.totient * d) := by
    rw [h_eq, hk]
    ring
  have h_le_ap : n + 1 ≤ A * p := by
    rw [h_p_eq]
    have h_le : q * d ≤ A * d := Nat.mul_le_mul_right d (by omega)
    have h_ring : A * (d + 1) = q * d + A + (A - q) * d := by
      have h_mul_sub : (A - q) * d = A * d - q * d := Nat.sub_mul A q d
      have h_mul_add : A * (d + 1) = A * d + A := by ring
      omega
    rw [h_ring]
    have h_div_eq2 : q * d = n + 1 - A := by
      rw [mul_comm, h_div_eq]
    rw [h_div_eq2]
    omega
  have h_ap_eq : A * p = k * (A.totient * d) + (n + 1) := Nat.eq_add_of_sub_eq h_le_ap h_eq2
  have h_eq3 : A * p - 1 = k * (A.totient * d) + n := by omega
  rw [h_eq3]
  have h_mod : (k * (A.totient * d) + n) % (A.totient * d) = n := by
    have h_rw : k * (A.totient * d) + n = n + (A.totient * d) * k := by ring
    rw [h_rw]
    rw [Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt h_ineq
  exact h_mod
