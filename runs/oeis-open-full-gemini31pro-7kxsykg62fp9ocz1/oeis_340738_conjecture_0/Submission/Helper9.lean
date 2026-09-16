import Mathlib
import Submission.Spec
import Submission.Helper6
import Submission.Helper7
import Submission.Helper8

open Nat Real

lemma J_odd_recurrence (k : ℕ) (hk : 2 ≤ k) :
  J (2 * k + 1) = (4 * (k : ℝ) + 2) * J (2 * k - 1) + J (2 * k - 3) := by
  dsimp [J]
  have ha := a_odd_pure_recurrence_int k hk
  have hb := b_odd_pure_recurrence_int k hk
  calc
    (A340737 (2 * k + 1) : ℝ) - (A340738 (2 * k + 1) : ℝ) * exp 1
      = (4 * (k:ℝ) + 2) * (A340737 (2 * k - 1) : ℝ) + (A340737 (2 * k - 3) : ℝ) -
        ((4 * (k:ℝ) + 2) * (A340738 (2 * k - 1) : ℝ) + (A340738 (2 * k - 3) : ℝ)) * exp 1 := by rw [ha, hb]
    _ = (4 * (k:ℝ) + 2) * ((A340737 (2 * k - 1) : ℝ) - (A340738 (2 * k - 1) : ℝ) * exp 1) +
        ((A340737 (2 * k - 3) : ℝ) - (A340738 (2 * k - 3) : ℝ) * exp 1) := by ring

lemma J_even_recurrence (k : ℕ) (hk : 2 ≤ k) :
  2 * J (2 * k) = (2 * (k : ℝ) + 1) * J (2 * k - 1) + J (2 * k - 3) := by
  dsimp [J]
  have ha := a_even_pure_recurrence_int k hk
  have hb := b_even_pure_recurrence_int k hk
  have h_b_eq : 2 * (A340737 (2 * k) : ℝ) = (2 * (k:ℝ) + 1) * (A340737 (2 * k - 1) : ℝ) + (A340737 (2 * k - 3) : ℝ) := hb
  have h_a_eq : 2 * (A340738 (2 * k) : ℝ) = (2 * (k:ℝ) + 1) * (A340738 (2 * k - 1) : ℝ) + (A340738 (2 * k - 3) : ℝ) := ha
  calc
    2 * ((A340737 (2 * k) : ℝ) - (A340738 (2 * k) : ℝ) * exp 1)
      = 2 * (A340737 (2 * k) : ℝ) - 2 * (A340738 (2 * k) : ℝ) * exp 1 := by ring
    _ = (2 * (k:ℝ) + 1) * (A340737 (2 * k - 1) : ℝ) + (A340737 (2 * k - 3) : ℝ) -
        ((2 * (k:ℝ) + 1) * (A340738 (2 * k - 1) : ℝ) + (A340738 (2 * k - 3) : ℝ)) * exp 1 := by rw [h_b_eq, h_a_eq]
    _ = (2 * (k:ℝ) + 1) * ((A340737 (2 * k - 1) : ℝ) - (A340738 (2 * k - 1) : ℝ) * exp 1) +
        ((A340737 (2 * k - 3) : ℝ) - (A340738 (2 * k - 3) : ℝ) * exp 1) := by ring

lemma J_odd_eq_I (k : ℕ) : J (2 * k + 1) = (-1 : ℝ)^k * I_k (k + 1) := by
  induction' k using Nat.strong_induction_on with k ih
  obtain rfl | hk1 := Nat.eq_zero_or_pos k
  · -- k = 0
    simp [J_1, I_1_val]
  · have hk1_le : 1 ≤ k := hk1
    obtain rfl | hk2 := eq_or_lt_of_le hk1_le
    · -- k = 1
      have hz : (-1 : ℝ)^1 = -1 := by norm_num
      rw [hz, J_3, I_2_val]
      ring
    · -- k >= 2
      have h_rec := J_odd_recurrence k hk2
      have ih1 := ih (k - 1) (by omega)
      have ih2 := ih (k - 2) (by omega)
      have eq1 : 2 * k - 1 = 2 * (k - 1) + 1 := by omega
      have eq2 : 2 * k - 3 = 2 * (k - 2) + 1 := by omega
      rw [eq1] at h_rec; rw [eq2] at h_rec
      rw [ih1, ih2] at h_rec
      have h_I_rec := I_k_recurrence (k) (by omega)
      have eq_I : I_k (k + 1) = - (4 * (k:ℝ) + 2) * I_k k + I_k (k - 1) := by linarith
      have hk_1 : (-1 : ℝ)^(k - 1) = - (-1 : ℝ)^k := by
        have : k = k - 1 + 1 := by omega
        nth_rw 2 [this]
        rw [pow_add, pow_one]
        ring
      have hk_2 : (-1 : ℝ)^(k - 2) = (-1 : ℝ)^k := by
        have : k = k - 2 + 2 := by omega
        nth_rw 2 [this]
        rw [pow_add, sq]
        ring
      have eq3 : k - 1 + 1 = k := by omega
      have eq4 : k - 2 + 1 = k - 1 := by omega
      rw [eq3] at h_rec
      rw [eq4] at h_rec
      rw [hk_1, hk_2] at h_rec
      rw [eq_I]
      linarith
