import Mathlib

open Nat

lemma totient_general_two_odd_prime_power_solution (q a b : ℕ) (ha : a ≥ 1) (hq_gt : q ≥ 3) (p : ℕ) (hp : p.Prime) (hp_gt : p ≥ q + 2) :
  (q^a * p^(b + 1) - 1) % (q^(a - 1) * (q - 1) * p^b * (p - 1)) = q^(a - 1) * p^b * (p + q - 1) - 1 := by
  have hp_gt2 : p ≥ q + 2 := hp_gt
  have h_q_pow : q^a = q^(a - 1) * q := by
    have : a = (a - 1) + 1 := by omega
    nth_rw 1 [this]
    rw [pow_succ]
  have h1 : q^a * p^(b + 1) - 1 = (q^(a - 1) * (q - 1) * p^b * (p - 1)) + (q^(a - 1) * p^b * (p + q - 1) - 1) := by
    rw [h_q_pow]
    rw [pow_succ]
    generalize hA : q^(a - 1) = A
    generalize hB : p^b = B
    have hq_eq : q = (q - 1) + 1 := by omega
    have hp_eq : p = (p - 1) + 1 := by omega
    generalize h_q1 : q - 1 = q1
    generalize h_p1 : p - 1 = p1
    have hA_pos : 1 ≤ A := by
      rw [← hA]
      exact Nat.one_le_pow _ q (by omega)
    have hB_pos : 1 ≤ B := by
      rw [← hB]
      exact Nat.one_le_pow _ p hp.pos
    have h_ring : A * (q1 + 1) * (B * (p1 + 1)) = A * q1 * B * p1 + A * B * (p1 + q1 + 1) := by ring
    have h_pos : 1 ≤ A * B * (p1 + q1 + 1) := by
      have : 0 < A * B * (p1 + q1 + 1) := mul_pos (mul_pos hA_pos hB_pos) (by omega)
      omega
    rw [hq_eq, hp_eq, h_q1, h_p1]
    have h_temp : p1 + 1 + (q1 + 1) - 1 = p1 + q1 + 1 := by omega
    rw [h_temp]
    rw [h_ring]
    rw [Nat.add_sub_assoc h_pos]
  rw [h1]
  have h5 : q^(a - 1) * p^b * (p + q - 1) - 1 < q^(a - 1) * (q - 1) * p^b * (p - 1) := by
    generalize hA : q^(a - 1) = A
    generalize hB : p^b = B
    have hA_pos : 1 ≤ A := by
      rw [← hA]
      exact Nat.one_le_pow _ q (by omega)
    have hB_pos : 1 ≤ B := by
      rw [← hB]
      exact Nat.one_le_pow _ p hp.pos
    have hq_ge : 3 ≤ q := hq_gt
    have hp_ge : 5 ≤ p := by omega
    generalize h_q1 : q - 1 = q1
    generalize h_p1 : p - 1 = p1
    have hq1_ge : 2 ≤ q1 := by omega
    have hp1_ge : 4 ≤ p1 := by omega
    have h_ineq : p1 + q1 + 1 < q1 * p1 := by nlinarith
    have h_left : A * B * (p + q - 1) = (A * B) * (p1 + q1 + 1) := by
      have : p + q - 1 = p1 + q1 + 1 := by omega
      rw [this]
    have h_right : A * q1 * B * p1 = (A * B) * (q1 * p1) := by ring
    rw [h_left, h_right]
    have h_diff_pos : 0 < q1 * p1 - (p1 + q1 + 1) := by omega
    have h_mul_diff_pos : 0 < (A * B) * (q1 * p1 - (p1 + q1 + 1)) := mul_pos (mul_pos hA_pos hB_pos) h_diff_pos
    have h_expand : (A * B) * (q1 * p1 - (p1 + q1 + 1)) = A * B * (q1 * p1) - A * B * (p1 + q1 + 1) := by
      rw [Nat.mul_sub_left_distrib]
    rw [h_expand] at h_mul_diff_pos
    omega
  rw [Nat.add_mod_left]
  exact Nat.mod_eq_of_lt h5
