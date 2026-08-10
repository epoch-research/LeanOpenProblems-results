import Mathlib

open Nat Set

lemma totient_general_solution (a b c q : ℕ) (hq_gt : q ≥ 2) (hb : b ≥ 1) (p : ℕ) (hp : p.Prime) (hp_gt : p ≥ q + 2) :
  (2^a * q^b * p^(c + 1) - 1) % (2^a * q^(b - 1) * p^c * (p - 1)) = 2^a * q^b * p^c - 1 := by
  have h_q_pow : q^b = q^(b - 1) * q := by
    have : b = (b - 1) + 1 := by omega
    nth_rw 1 [this]
    rw [pow_succ]
  have h1 : 2^a * q^b * p^(c + 1) - 1 = q * (2^a * q^(b - 1) * p^c * (p - 1)) + (2^a * q^b * p^c - 1) := by
    rw [h_q_pow]
    rw [pow_succ]
    generalize hA : 2^a = A
    generalize hB : q^(b - 1) = B
    generalize hC : p^c = C
    have hp_eq : p = (p - 1) + 1 := by omega
    nth_rw 1 [hp_eq]
    rw [mul_add, mul_one]
    generalize hC_p : C * (p - 1) = C_p
    have h_expand : A * (B * q) * (C_p + C) = A * B * q * C_p + A * B * q * C := by ring
    rw [h_expand]
    have h_assoc1 : A * B * q * C_p = q * (A * B * C_p) := by ring
    rw [h_assoc1]
    have h_assoc3 : q * (A * B * C_p) = q * (A * B * C * (p - 1)) := by
      rw [← hC_p]
      ring
    rw [h_assoc3]
    have hA_pos : 1 ≤ A := by
      rw [← hA]
      exact Nat.one_le_pow _ 2 (by omega)
    have hB_pos : 1 ≤ B := by
      rw [← hB]
      exact Nat.one_le_pow _ q (by omega)
    have hC_pos : 1 ≤ C := by
      rw [← hC]
      exact Nat.one_le_pow _ p hp.pos
    generalize hX : q * (A * B * C * (p - 1)) = X
    have h_assoc_Y : A * (B * q) * C = A * B * q * C := by ring
    rw [h_assoc_Y]
    generalize hY : A * B * q * C = Y
    have hY_pos : 0 < Y := by
      rw [← hY]
      have hA_pos_pos : 0 < A := by omega
      have hB_pos_pos : 0 < B := by omega
      have hC_pos_pos : 0 < C := by omega
      exact mul_pos (mul_pos (mul_pos hA_pos_pos hB_pos_pos) (by omega)) hC_pos_pos
    omega
  rw [h1]
  have h5 : 2^a * q^b * p^c - 1 < 2^a * q^(b - 1) * p^c * (p - 1) := by
    rw [h_q_pow]
    generalize hA : 2^a = A
    generalize hB : q^(b - 1) = B
    generalize hC : p^c = C
    have hp1 : q + 1 ≤ p - 1 := by omega
    have hA_pos : 1 ≤ A := by
      rw [← hA]
      exact Nat.one_le_pow _ 2 (by omega)
    have hB_pos : 1 ≤ B := by
      rw [← hB]
      exact Nat.one_le_pow _ q (by omega)
    have hC_pos : 1 ≤ C := by
      rw [← hC]
      exact Nat.one_le_pow _ p hp.pos
    have h6 : A * B * C * q ≤ A * B * C * (p - 1) := Nat.mul_le_mul_left (A * B * C) (by omega)
    have h7 : A * B * C * q = A * (B * q) * C := by ring
    rw [h7] at h6
    generalize hX : A * (B * q) * C = X
    generalize hY : A * B * C * (p - 1) = Y
    have hX_pos : 0 < X := by
      rw [← hX]
      have hA_pos_pos : 0 < A := by omega
      have hB_pos_pos : 0 < B := by omega
      have hC_pos_pos : 0 < C := by omega
      exact mul_pos (mul_pos hA_pos_pos (mul_pos hB_pos_pos (by omega))) hC_pos_pos
    omega
  rw [Nat.add_comm]
  rw [Nat.add_mul_mod_self_right]
  exact Nat.mod_eq_of_lt h5
