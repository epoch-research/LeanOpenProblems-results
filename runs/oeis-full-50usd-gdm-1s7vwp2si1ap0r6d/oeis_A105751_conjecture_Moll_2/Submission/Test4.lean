import Mathlib

theorem val_eq_of_dvd_not_dvd {y : ℤ} {k : ℕ} (hy0 : y ≠ 0) (h1 : (2:ℤ)^k ∣ y) (h2 : ¬ (2:ℤ)^(k+1) ∣ y) : padicValInt 2 y = k := by
  have h_prime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hy0' : y.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hy0
  have hd1 : 2^k ∣ y.natAbs := by
    rwa [← Int.natCast_dvd, Int.natCast_pow, Int.natCast_ofNat] at h1
  have hd2 : ¬ 2^(k+1) ∣ y.natAbs := by
    intro hc
    apply h2
    rwa [← Int.natCast_dvd, Int.natCast_pow, Int.natCast_ofNat]
  rw [padicValInt, padicValNat_dvd_iff_le hy0'] at hd1 hd2
  omega
