import Submission.Lemmas9
import Mathlib

lemma record_le_n (R : ℕ) (h1 : 5 < R) (h2 : is_difference_record R) :
  ∃ n, 2 ≤ n ∧ d n = R ∧ R ≤ n := by
  rcases h2 with ⟨n, hn, hd_eq, h_max⟩
  use n
  refine ⟨hn, hd_eq, ?_⟩
  have hd_eq2 : d n = R := hd_eq
  have : d n =
    if n % 2 = 0 then
      Nat.gcd n (C (n - 1) - 1)
    else
      Nat.gcd (n - 2) (C (n - 1) + 1) := d_val2 n hn
  rw [this] at hd_eq2
  split_ifs at hd_eq2 with h_even
  · have h_d_div : R ∣ n := by rw [← hd_eq2]; exact Nat.gcd_dvd_left _ _
    exact Nat.le_of_dvd (by omega) h_d_div
  · have h_d_div : R ∣ n - 2 := by rw [← hd_eq2]; exact Nat.gcd_dvd_left _ _
    by_cases h_z : n - 2 = 0
    · rw [h_z] at h_d_div
      have hR : R = Nat.gcd (n - 2) (C (n - 1) + 1) := hd_eq2.symm
      rw [h_z, Nat.gcd_zero_left] at hR
      have hR2 : R = C 1 + 1 := by
        have : n = 2 := by omega
        rw [this] at hR
        exact hR
      have : C 1 = 1 := rfl
      rw [this] at hR2
      omega
    · have h_pos : 0 < n - 2 := by omega
      have h1_le : R ≤ n - 2 := Nat.le_of_dvd h_pos h_d_div
      omega

