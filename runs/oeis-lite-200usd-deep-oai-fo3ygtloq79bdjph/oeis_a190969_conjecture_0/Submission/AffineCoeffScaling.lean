import FormalConjectures.Util.ProblemImports

open Polynomial Finset Nat
open scoped BigOperators

/-- For `p=2n+1`, the binomial coefficients that could contribute from degrees
above `p-1=2n` in an affine change vanish modulo `p`. -/
lemma prime_dvd_choose_two_mul_add {p n t : ℕ} (hp : p.Prime) (hp_eq : p = 2 * n + 1)
    (htpos : 1 ≤ t) (htle : t ≤ n) :
    p ∣ (2 * n + t).choose (2 * n) := by
  have ha_lt : 2 * n < p := by omega
  have hsub : 2 * n + t - 2 * n = t := by omega
  have hbsub_lt : 2 * n + t - 2 * n < p := by omega
  have hp_le : p ≤ 2 * n + t := by omega
  simpa [hsub] using hp.dvd_choose (a := 2 * n) (b := 2 * n + t) ha_lt hbsub_lt hp_le

lemma choose_two_mul_add_cast_zero_zmod {p n t : ℕ} (hp : p.Prime) (hp_eq : p = 2 * n + 1)
    (htpos : 1 ≤ t) (htle : t ≤ n) :
    (((2 * n + t).choose (2 * n) : ℕ) : ZMod p) = 0 := by
  rw [ZMod.natCast_eq_zero_iff]
  exact prime_dvd_choose_two_mul_add hp hp_eq htpos htle

/-- A monic affine high-degree term does not contribute to the `X^(2n)` coefficient modulo `p`.
This is the core binomial-vanishing fact needed for affine coefficient scaling; the scaled version
requires one more routine coefficient calculation. -/
lemma coeff_monic_affine_high_term_zero_zmod {p n t : ℕ} (hp : p.Prime) (hp_eq : p = 2 * n + 1)
    (htpos : 1 ≤ t) (htle : t ≤ n) (r : ZMod p) :
    (((X : (ZMod p)[X]) + C r) ^ (2 * n + t)).coeff (2 * n) = 0 := by
  rw [coeff_X_add_C_pow]
  rw [choose_two_mul_add_cast_zero_zmod hp hp_eq htpos htle]
  simp
