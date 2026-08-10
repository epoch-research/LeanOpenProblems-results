import Mathlib

theorem valuation_one_add_sq_even (m : ℤ) (h : m % 2 = 0) : padicValInt 2 (1 + m^2) = 0 := by
  unfold padicValInt
  apply padicValNat.eq_zero_of_not_dvd
  intro hc
  have h_dvd : (2 : ℤ) ∣ (1 + m^2) := by
    rwa [← Int.ofNat_dvd_left] at hc
  have h_mod : (1 + m^2) % 2 = 1 := by
    have hm : m = 2 * (m / 2) := by omega
    set k := m / 2
    rw [hm]
    have : 1 + (2 * k)^2 = 2 * (2 * k^2) + 1 := by ring
    rw [this]
    omega
  have h_hc : (1 + m^2) % 2 = 0 := Int.dvd_iff_emod_eq_zero.mp h_dvd
  omega
