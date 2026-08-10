import Mathlib

theorem valuation_one_add_sq (m : ℤ) : padicValInt 2 (1 + m^2) = if m % 2 = 0 then 0 else 1 := by
  have h_prime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases h : m % 2 = 0
  · -- Even case
    simp only [h, ↓reduceIte]
    have h_odd : ¬ 2 ∣ (1 + m^2) := by
      intro hc
      have h_mod : (1 + m^2) % 2 = 0 := Int.dvd_iff_emod_eq_zero.mp hc
      have hm : m % 2 = 0 := h
      omega
    rw [padicValInt.eq_zero_of_not_dvd h_odd]
  · -- Odd case
    have h_odd : m % 2 = 1 ∨ m % 2 = -1 := by omega
    simp only [h, ↓reduceIte]
    have h_div : (2 : ℤ) ∣ (1 + m^2) := by
      rcases h_odd with h1 | h1
      · use 2 * (m / 2)^2 + 2 * (m / 2) + 1
        have : m = 2 * (m / 2) + 1 := by omega
        nth_rw 1 [this]
        ring
      · use 2 * (m / 2)^2 + 2 * (m / 2) + 1 -- wait, if m % 2 = -1, m = 2 * (m / 2) - 1 or similar
        sorry
    sorry
