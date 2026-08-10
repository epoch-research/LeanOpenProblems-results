import Mathlib

theorem valuation_one_add_sq_odd (m : ℤ) (h : m % 2 = 1) : padicValInt 2 (1 + m^2) = 1 := by
  have h_prime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h_eq : 1 + m^2 = 2 * (2 * (m / 2)^2 + 2 * (m / 2) + 1) := by
    have : m = 2 * (m / 2) + 1 := by omega
    nth_rw 1 [this]
    ring
  have h_odd : ¬ (2 : ℤ) ∣ (2 * (m / 2)^2 + 2 * (m / 2) + 1) := by
    intro hc
    rcases hc with ⟨d, hd⟩
    omega
  have h_eq_zero : padicValInt 2 (2 * (m / 2)^2 + 2 * (m / 2) + 1) = 0 := by
    unfold padicValInt
    apply padicValNat.eq_zero_of_not_dvd
    intro hc
    apply h_odd
    rwa [← Int.ofNat_dvd_left] at hc
  rw [h_eq]
  rw [padicValInt.mul]
  · have h2 : padicValInt 2 2 = 1 := by
      unfold padicValInt
      norm_num
    rw [h2, h_eq_zero, add_zero]
  · norm_num
  · intro hc
    have : (2 * (m / 2)^2 + 2 * (m / 2) + 1) = 0 := by omega
    rw [hc] at this
    norm_num at this
