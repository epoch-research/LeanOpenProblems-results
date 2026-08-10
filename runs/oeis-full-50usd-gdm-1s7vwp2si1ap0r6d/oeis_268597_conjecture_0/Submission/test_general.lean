import Mathlib

open Nat

lemma totient_divisor_sol_general (d : ℕ) (q : ℕ) (hq : q.Prime) 
    (c : ℕ) (w : ℕ) (k : ℕ) (hk : k ≥ 1) (h_dk : d ≥ k) (h_eq_w : w - d = k * (q - 1)) 
    (h_div : d.totient ∣ d - k) (h_ineq : d.totient * (q - 1) ≥ w) :
    (d * q^(c+1) - 1) % (d.totient * q^c * (q - 1)) = w * q^c - 1 := by
  have hd_pos : d > 0 := by omega
  have hq_pos : q > 0 := by
    have : q ≥ 2 := hq.two_le
    omega
  have h_qc_pos : q^c > 0 := by positivity
  have h_d_qc_pos : d * q^c > 0 := Nat.mul_pos hd_pos h_qc_pos
  have hq_ge : q ≥ 2 := hq.two_le
  have hq1 : q - 1 ≥ 1 := by omega
  have hkq1 : k * (q - 1) ≥ 1 := by
    calc k * (q - 1)
      _ ≥ 1 * 1 := Nat.mul_le_mul hk hq1
      _ = 1 := by rfl
  have hw : w = d + k * (q - 1) := by omega
  have hw_pos : w > 0 := by omega
  have hw_qc_pos : w * q^c > 0 := Nat.mul_pos hw_pos h_qc_pos
  have hd_q : d * q = (d - k) * (q - 1) + w := by
    rw [hw]
    set X := d - k
    set Y := q - 1
    have h1 : X * Y + (d + k * Y) = (X + k) * Y + d := by ring
    rw [h1]
    rw [Nat.sub_add_cancel h_dk]
    rw [mul_tsub, mul_one]
    rw [Nat.sub_add_cancel]
    apply Nat.le_mul_of_pos_right
    exact hq_pos
  obtain ⟨m, hm⟩ := h_div
  have h_eq : d * q^(c+1) - 1 = m * (d.totient * q^c * (q - 1)) + (w * q^c - 1) := by
    rw [pow_succ q c]
    have h1 : d * (q^c * q) = q^c * (d * q) := by ring
    rw [h1]
    rw [hd_q, hm]
    have h_sub : q^c * (d.totient * m * (q - 1) + w) - 1 = m * (d.totient * q^c * (q - 1)) + w * q^c - 1 := by
      set Y := q - 1
      have : q^c * (d.totient * m * Y + w) = m * (d.totient * q^c * Y) + w * q^c := by ring
      rw [this]
    rw [h_sub]
    rw [Nat.add_sub_assoc hw_qc_pos]
  rw [h_eq]
  have h_mod : (m * (d.totient * q^c * (q - 1)) + (w * q^c - 1)) % (d.totient * q^c * (q - 1)) = (w * q^c - 1) % (d.totient * q^c * (q - 1)) := by
    rw [add_comm]
    set Y := d.totient * q^c * (q - 1)
    have h_comm : m * Y = Y * m := mul_comm m Y
    rw [h_comm]
    rw [Nat.add_mul_mod_self_left]
  rw [h_mod]
  apply Nat.mod_eq_of_lt
  have : w * q^c - 1 < w * q^c := Nat.sub_lt hw_qc_pos (by decide)
  have : w * q^c ≤ d.totient * q^c * (q - 1) := by
    have h_mul_ineq : d.totient * (q - 1) * q^c ≥ w * q^c := Nat.mul_le_mul_right (q^c) h_ineq
    set Y := q - 1
    have : d.totient * q^c * Y = d.totient * Y * q^c := by ring
    rw [this]
    exact h_mul_ineq
  omega



theorem test_interval (n : ℕ) (hn : n < 5) : ∃ x > 0, (x - 1) % Nat.totient x = n := by
  interval_cases n
  · use 1; decide
  · use 4; decide
  · use 9; decide
  · use 8; decide
  · use 25; decide
