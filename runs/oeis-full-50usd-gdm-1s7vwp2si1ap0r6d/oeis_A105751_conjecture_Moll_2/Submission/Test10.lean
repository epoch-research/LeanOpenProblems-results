import Mathlib

theorem valuation_one_add_sq (m : ℤ) : padicValInt 2 (1 + m^2) = if m % 2 = 0 then 0 else 1 := by
  have h_prime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h_mod_cases : m % 2 = 0 ∨ m % 2 = 1 := by omega
  rcases h_mod_cases with h | h
  · -- Even case
    simp [h]
    have h_odd : ¬ 2 ∣ (1 + m^2) := by
      intro hc
      have h_mod : (1 + m^2) % 2 = 0 := Int.dvd_iff_emod_eq_zero.mp hc
      omega
    rw [padicValInt.eq_zero_of_not_dvd h_odd]
  · -- Odd case
    have h_not : ¬ m % 2 = 0 := by omega
    simp [h_not]
    have h_eq : 1 + m^2 = 2 * (2 * (m / 2)^2 + 2 * (m / 2) + 1) := by
      have : m = 2 * (m / 2) + 1 := by omega
      nth_rw 1 [this]
      ring
    have h_odd : ¬ 2 ∣ (2 * (m / 2)^2 + 2 * (m / 2) + 1) := by
      intro hc
      have h_mod : (2 * (m / 2)^2 + 2 * (m / 2) + 1) % 2 = 0 := Int.dvd_iff_emod_eq_zero.mp hc
      omega
    rw [h_eq]
    rw [padicValInt.mul]
    · rw [padicValInt.self (by norm_num : 1 < 2), padicValInt.eq_zero_of_not_dvd h_odd, add_zero]
    · norm_num
    · intro hc
      have : (2 * (m / 2)^2 + 2 * (m / 2) + 1) % 2 = 1 := by omega
      rw [hc] at this
      norm_num at this
