import Mathlib

theorem valuation_one_add_sq (m : ℤ) : padicValInt 2 (1 + m^2) = if m % 2 = 0 then 0 else 1 := by
  have h_prime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h_mod_cases : m % 2 = 0 ∨ m % 2 = 1 := by omega
  rcases h_mod_cases with h | h
  · -- Even case
    have h_not_dvd : ¬ (2 : ℤ) ∣ (1 + m^2) := by
      intro hc
      rcases hc with ⟨d, hd⟩
      have hm : m = 2 * (m / 2) := by omega
      rw [hm] at hd
      omega
    have h_eq_zero : padicValInt 2 (1 + m^2) = 0 := by
      rw [padicValInt]
      have h_nat : (1 + m^2).natAbs ≠ 0 := by
        have hm : m = 2 * (m / 2) := by omega
        rw [hm]
        omega
      rw [padicValNat.eq_zero_iff]
      right; right; left
      intro hc
      apply h_not_dvd
      rwa [← Int.ofNat_dvd_left]
    rw [h_eq_zero]
    simp [h]
  · -- Odd case
    have h_eq : 1 + m^2 = 2 * (2 * (m / 2)^2 + 2 * (m / 2) + 1) := by
      have : m = 2 * (m / 2) + 1 := by omega
      nth_rw 1 [this]
      ring
    have h_odd : ¬ (2 : ℤ) ∣ (2 * (m / 2)^2 + 2 * (m / 2) + 1) := by
      intro hc
      rcases hc with ⟨d, hd⟩
      omega
    have h_eq_zero : padicValInt 2 (2 * (m / 2)^2 + 2 * (m / 2) + 1) = 0 := by
      rw [padicValInt]
      have h_nat : (2 * (m / 2)^2 + 2 * (m / 2) + 1).natAbs ≠ 0 := by omega
      rw [padicValNat.eq_zero_iff]
      right; right; left
      intro hc
      apply h_odd
      rwa [← Int.ofNat_dvd_left]
    have h_not : ¬ m % 2 = 0 := by omega
    simp [h_not]
    rw [h_eq]
    rw [padicValInt.mul]
    · rw [padicValInt.self (by norm_num : 1 < 2), h_eq_zero]
    · norm_num
    · intro hc
      have : (2 * (m / 2)^2 + 2 * (m / 2) + 1) = 0 := by omega
      rw [hc] at this
      norm_num at this
