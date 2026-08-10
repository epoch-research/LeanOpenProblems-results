import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 200000
open Nat

lemma coprime_dvd_mul {q c A B : ℕ} (hq : Nat.Prime q) (h_coprime : Nat.Coprime A B) (h_dvd : q^c ∣ A * B) :
  q^c ∣ A ∨ q^c ∣ B := by
  by_cases hqA : q ∣ A
  · left
    have hqB : ¬ q ∣ B := by
      intro hqB
      have h_div : q ∣ Nat.gcd A B := Nat.dvd_gcd hqA hqB
      rw [h_coprime.gcd_eq_one] at h_div
      exact Nat.Prime.not_dvd_one hq h_div
    have h_cop : Nat.Coprime (q^c) B := hq.coprime_iff_not_dvd.mpr hqB |>.pow_left c
    have h_dvd' : q^c ∣ B * A := by rw [Nat.mul_comm B A]; exact h_dvd
    exact h_cop.dvd_of_dvd_mul_left h_dvd'
  · right
    have h_cop : Nat.Coprime (q^c) A := hq.coprime_iff_not_dvd.mpr hqA |>.pow_left c
    have h_dvd' : q^c ∣ A * B := h_dvd
    exact h_cop.dvd_of_dvd_mul_left h_dvd'






