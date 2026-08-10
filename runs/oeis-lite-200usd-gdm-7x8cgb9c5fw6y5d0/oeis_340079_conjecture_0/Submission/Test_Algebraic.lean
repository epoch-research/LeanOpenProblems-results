import FormalConjectures.Util.ProblemImports

open Nat BigOperators Finset

lemma test_algebraic {q k Y a b : ℕ} (hq : Nat.Prime q) (hr_prime : Nat.Prime k.minFac)
    (hqr_lt : q < k.minFac) (ha : 3 * (2 * k.minFac - 1) * Y - 1 = q * a)
    (hb : 3 * (2 * q - 1) * Y - 1 = k.minFac * b) (h_yk : Y ≥ 1) (hq2 : 2 < q) :
    a > 6 * Y ∧ b < 6 * Y := by
  have hqr_le : q ≤ k.minFac := Nat.le_of_lt hqr_lt
  have hq_ge3 : q ≥ 3 := by omega
  have ha_gt : a > 6 * Y := by
    have h_mul : q * (6 * Y) < q * a := by
      rw [← ha]
      have h_le_mul : (q + 1) * (6 * Y) ≤ k.minFac * (6 * Y) := Nat.mul_le_mul_right (6 * Y) (by omega)
      have h_sub1 : 3 * (2 * k.minFac - 1) * Y = 6 * k.minFac * Y - 3 * Y := by
        have h_step : 3 * (2 * k.minFac - 1) = 6 * k.minFac - 3 := by
          rw [Nat.mul_sub_left_distrib]
          omega
        rw [h_step, Nat.sub_mul]
      have h_sub2 : (q + 1) * (6 * Y) = 6 * q * Y + 6 * Y := by ring
      have h_sub3 : k.minFac * (6 * Y) = 6 * k.minFac * Y := by ring
      have h_sub4 : q * (6 * Y) = 6 * q * Y := by ring
      rw [h_sub1, h_sub4]
      rw [h_sub2, h_sub3] at h_le_mul
      omega
    exact Nat.lt_of_mul_lt_mul_left h_mul
  have hb_lt : b < 6 * Y := by
    have h_mul : b * k.minFac < 6 * Y * k.minFac := by
      rw [mul_comm b k.minFac, ← hb]
      have h_step : 3 * (2 * q - 1) * Y < 6 * Y * k.minFac := by
        have h_lt_mul : q * (6 * Y) < k.minFac * (6 * Y) := Nat.mul_lt_mul_of_pos_right hqr_lt (by omega)
        have h_sub1 : 3 * (2 * q - 1) * Y = 6 * q * Y - 3 * Y := by
          have h_step : 3 * (2 * q - 1) = 6 * q - 3 := by
            rw [Nat.mul_sub_left_distrib]
            omega
          rw [h_step, Nat.sub_mul]
        have h_sub2 : q * (6 * Y) = 6 * q * Y := by ring
        have h_sub3 : k.minFac * (6 * Y) = 6 * Y * k.minFac := by ring
        rw [h_sub1]
        rw [h_sub2, h_sub3] at h_lt_mul
        omega
      omega
    exact Nat.lt_of_mul_lt_mul_right h_mul
  exact ⟨ha_gt, hb_lt⟩
