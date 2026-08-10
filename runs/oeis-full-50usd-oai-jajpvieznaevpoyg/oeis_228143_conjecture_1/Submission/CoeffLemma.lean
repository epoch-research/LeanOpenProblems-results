import FormalConjectures.Util.ProblemImports
open PowerSeries BigOperators Finset

lemma coeff_mul_X_pow_eq_zero_of_lt (R) [Semiring R] (f : PowerSeries R) {n d : ℕ} (h : n < d) :
    PowerSeries.coeff n (f * (PowerSeries.X : PowerSeries R)^d) = 0 := by
  rw [PowerSeries.coeff_mul_X_pow']
  simp [h]

lemma coeff_pow7_mul_monomial_high (n : ℕ) (P : PowerSeries ℤ) (c : ℤ)
    (hP0 : PowerSeries.coeff 0 P = 1) :
    PowerSeries.coeff (n+1) (P ^ 7 * PowerSeries.monomial (n+1) c) = c := by
  rw [PowerSeries.monomial_eq_C_mul_X_pow]
  rw [← mul_assoc]
  rw [PowerSeries.coeff_mul_X_pow']
  have hc : PowerSeries.constantCoeff P = 1 := by
    simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hP0
  simp [hc]

lemma coeff_error_high (n : ℕ) (S : PowerSeries ℤ) (c : ℤ) :
    PowerSeries.coeff (n+1) ((PowerSeries.monomial (n+1) c)^2 * S) = 0 := by
  rw [PowerSeries.monomial_eq_C_mul_X_pow]
  rw [show (PowerSeries.C c * (PowerSeries.X : PowerSeries ℤ) ^ (n+1)) ^ 2 * S =
      ((PowerSeries.C c)^2 * S) * (PowerSeries.X : PowerSeries ℤ) ^ (2*(n+1)) by ring]
  rw [PowerSeries.coeff_mul_X_pow']
  have h : n + 1 < 2 * (n + 1) := by omega
  simp [h]

lemma coeff_pow8_add_monomial_high (n : ℕ) (P : PowerSeries ℤ) (c : ℤ)
    (hP0 : PowerSeries.coeff 0 P = 1) :
    PowerSeries.coeff (n+1) ((P + PowerSeries.monomial (n+1) c) ^ 8)
      = PowerSeries.coeff (n+1) (P ^ 8) + 8 * c := by
  let M : PowerSeries ℤ := PowerSeries.monomial (n+1) c
  let S : PowerSeries ℤ :=
    28 • P^6 + 56 • (P^5*M) + 70 • (P^4*M^2) + 56 • (P^3*M^3) +
    28 • (P^2*M^4) + 8 • (P*M^5) + M^6
  have hid : (P + M)^8 = P^8 + 8 • (P^7 * M) + M^2 * S := by
    dsimp [S]
    ring
  change PowerSeries.coeff (n+1) ((P + M)^8) = PowerSeries.coeff (n+1) (P^8) + 8*c
  rw [hid]
  simp only [map_add, map_nsmul]
  rw [coeff_pow7_mul_monomial_high n P c hP0]
  have herr : PowerSeries.coeff (n+1) (M^2 * S) = 0 := by
    dsimp [M]
    exact coeff_error_high n S c
  rw [herr]
  simp

lemma coeff_pos_pow8_one_add_two_dvd16 (E : PowerSeries ℤ) {m : ℕ} (hm : 0 < m) :
    (16 : ℤ) ∣ PowerSeries.coeff m ((1 + 2 • E) ^ 8) := by
  let S : PowerSeries ℤ := E + 7 • E^2 + 28 • E^3 + 70 • E^4 + 112 • E^5 + 112 • E^6 + 64 • E^7 + 16 • E^8
  have hid : (1 + 2 • E)^8 = 1 + 16 • S := by
    dsimp [S]
    ring
  rw [hid]
  use PowerSeries.coeff m S
  simp [hm.ne']
  change PowerSeries.coeff m (PowerSeries.C (16 : ℤ) * S) = 16 * PowerSeries.coeff m S
  rw [PowerSeries.coeff_C_mul]
