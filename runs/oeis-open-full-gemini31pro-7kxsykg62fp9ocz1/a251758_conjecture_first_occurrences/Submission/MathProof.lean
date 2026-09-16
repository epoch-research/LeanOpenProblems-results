import Submission.Spec
import Mathlib

open Nat List Finset

lemma no_divisor_between {n p x : ℕ} (hn : n ≥ 2) (hp : p = minFac n) 
    (hx : n / p < x) (hx2 : x < n) (hdiv : x ∣ n) : False := by
  rcases hdiv with ⟨k, hk⟩
  have hp_dvd : p ∣ n := by rw [hp]; exact minFac_dvd n
  have hk0 : k ≠ 0 := by
    rintro rfl
    have : n = 0 := by rw [hk, mul_zero]
    omega
  have hp0 : p ≠ 0 := by
    have : p ≥ 2 := by rw [hp]; exact minFac_prime (by omega) |>.two_le
    omega
  have h_k_gt_1 : 1 < k := by
    have : k ≠ 1 := by
      rintro rfl
      have : n = x := by rw [hk, mul_one]
      omega
    have : k ≠ 0 := hk0
    omega
  have h_k_lt_p : k < p := by
    by_contra h_not
    have h_ge : p ≤ k := Nat.ge_of_not_lt h_not
    have h1 : p * x ≤ k * x := Nat.mul_le_mul_right x h_ge
    have h2 : k * x = n := by rw [mul_comm]; exact hk.symm
    have hx3 : n / p * p < x * p := Nat.mul_lt_mul_of_pos_right hx (by omega)
    have h4 : n / p * p = n := Nat.div_mul_cancel hp_dvd
    have h5 : x * p = p * x := mul_comm _ _
    rw [h4, h5] at hx3
    omega
  have k_dvd : k ∣ n := ⟨x, by rw [mul_comm] at hk; exact hk⟩
  have p_le_k := minFac_le_of_dvd h_k_gt_1 k_dvd
  rw [← hp] at p_le_k
  omega

