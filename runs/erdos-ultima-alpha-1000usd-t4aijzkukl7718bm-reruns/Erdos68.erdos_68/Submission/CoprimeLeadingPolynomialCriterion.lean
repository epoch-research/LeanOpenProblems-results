import Submission.MonicPolynomialCriterion

/-! Several small polynomials can replace a single monic polynomial if their
leading coefficients generate the unit ideal. This is a criterion only. -/

namespace CoprimeLeadingPolynomialCriterion

open Polynomial

lemma integer_of_common_roots {ι : Type*} [Fintype ι]
    (P : ι → ℤ[X]) (u : ι → ℤ)
    (hu : ∑ i, u i * (P i).leadingCoeff = 1)
    (r : ℚ) (hr : ∀ i, aeval r (P i) = 0) :
    ∃ z : ℤ, (z : ℚ) = r := by
  have hd : (IsFractionRing.den ℤ r : ℤ) ∣ 1 := by
    rw [← hu]
    exact Finset.dvd_sum (fun i _ =>
      dvd_mul_of_dvd_right (den_dvd_of_is_root (hr i)) (u i))
  obtain ⟨z, hz⟩ := IsFractionRing.isInteger_of_isUnit_den
    (isUnit_of_dvd_one hd)
  exact ⟨z, by simpa using hz⟩

/-- Each error is compared to the denominator bound for its own actual degree. -/
theorem irrational_of_small_polynomials (x : ℝ)
    (hx : ∀ z : ℤ, (z : ℝ) ≠ x)
    (h : ∀ b : ℕ, 0 < b → ∃ k : ℕ, ∃ P : Fin k → ℤ[X], ∃ u : Fin k → ℤ,
      (∑ i, u i * (P i).leadingCoeff = 1) ∧
      ∀ i, |aeval x (P i)| < 1 / (b : ℝ) ^ (P i).natDegree) :
    Irrational x := by
  rintro ⟨r, rfl⟩
  obtain ⟨k, P, u, hu, hsmall⟩ := h r.den r.den_pos
  have hroot (i : Fin k) : aeval r (P i) = 0 := by
    apply Rat.cast_injective (α := ℝ)
    simpa [MonicPolynomialCriterion.cast_aeval] using
      MonicPolynomialCriterion.rational_small_polynomial_zero (P i) r (hsmall i)
  obtain ⟨z, hz⟩ := integer_of_common_roots P u hu r hroot
  apply hx z
  exact_mod_cast hz

end CoprimeLeadingPolynomialCriterion

#print axioms CoprimeLeadingPolynomialCriterion.integer_of_common_roots
#print axioms CoprimeLeadingPolynomialCriterion.irrational_of_small_polynomials
