import Submission.MonicPolynomialCriterion

/-! A nonvanishing criterion for auxiliary polynomials with constant coefficient one.
This file does not construct the required small-polynomial family. -/

namespace UnitConstantPolynomialCriterion

open Polynomial

lemma reverse_monic_of_constant_one (P : ℤ[X]) (hP : P.coeff 0 = 1) :
    P.reverse.Monic := by
  have h0 : P.coeff 0 ≠ 0 := by omega
  have ht : P.natTrailingDegree = 0 := by
    exact (natTrailingDegree_eq_zero).mpr (Or.inr h0)
  change P.reverse.leadingCoeff = 1
  rw [reverse_leadingCoeff, trailingCoeff, ht, hP]

lemma rational_eval_ne_zero (P : ℤ[X]) (hP : P.coeff 0 = 1)
    (r : ℚ) (hr : 1 < r) : aeval r P ≠ 0 := by
  intro hroot
  have hr0 : r ≠ 0 := by linarith
  letI : Invertible r := invertibleOfNonzero hr0
  have hrev : aeval r⁻¹ P.reverse = 0 := by
    have h := (eval₂_reverse_eq_zero_iff (algebraMap ℤ ℚ) r P).mpr hroot
    simpa only [invOf_eq_inv, aeval_def] using h
  obtain ⟨z, hz, _⟩ := exists_integer_of_is_root_of_monic
    (reverse_monic_of_constant_one P hP) hrev
  change r⁻¹ = (z : ℚ) at hz
  have hzpos : (0 : ℚ) < z := by
    rw [← hz]
    exact inv_pos.mpr (by linarith)
  have hzlt : (z : ℚ) < 1 := by
    rw [← hz]
    exact inv_lt_one_of_one_lt₀ hr
  have : (0 : ℤ) < z := by exact_mod_cast hzpos
  have : z < (1 : ℤ) := by exact_mod_cast hzlt
  omega

/-- The error is compared with the denominator raised to the polynomial's degree.
A family merely having values tending to zero would not suffice. -/
theorem irrational_of_unit_constant_small_polynomials (x : ℝ) (hx : 1 < x)
    (h : ∀ b : ℕ, 0 < b → ∃ P : ℤ[X], P.coeff 0 = 1 ∧
      |aeval x P| < 1 / (b : ℝ) ^ P.natDegree) : Irrational x := by
  rintro ⟨r, rfl⟩
  obtain ⟨P, hP, hsmall⟩ := h r.den r.den_pos
  have hroot := MonicPolynomialCriterion.rational_small_polynomial_zero P r hsmall
  have hrQ : aeval r P = 0 := by
    apply Rat.cast_injective (α := ℝ)
    simpa [MonicPolynomialCriterion.cast_aeval] using hroot
  exact rational_eval_ne_zero P hP r (by exact_mod_cast hx) hrQ

end UnitConstantPolynomialCriterion

#print axioms UnitConstantPolynomialCriterion.rational_eval_ne_zero
#print axioms UnitConstantPolynomialCriterion.irrational_of_unit_constant_small_polynomials
