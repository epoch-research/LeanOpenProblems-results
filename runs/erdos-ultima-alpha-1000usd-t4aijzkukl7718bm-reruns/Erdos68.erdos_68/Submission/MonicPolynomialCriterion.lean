import FormalConjecturesUtil

/-! Monic auxiliary polynomials avoid rational nonintegral roots. This is a
criterion only: no suitable family is constructed for the conjectured sum. -/

namespace MonicPolynomialCriterion

open Polynomial

lemma scaled_rational_eval_integer (P : ℤ[X]) (r : ℚ) :
    ∃ z : ℤ, (r.den : ℝ) ^ P.natDegree * aeval (r : ℝ) P = z := by
  refine ⟨(P.scaleRoots (r.den : ℤ)).eval r.num, ?_⟩
  have hr : (r.den : ℝ) * (r : ℝ) = r.num := by
    rw [Rat.cast_def]
    have hd : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.den_ne_zero
    field_simp
  have h := Polynomial.scaleRoots_eval₂_mul (p := P)
    (Int.castRingHom ℝ) (r : ℝ) (r.den : ℤ)
  have hs : (Int.castRingHom ℝ) (r.den : ℤ) = (r.den : ℝ) := by simp
  rw [hs, hr] at h
  have hev : eval₂ (Int.castRingHom ℝ) (r.num : ℝ) (P.scaleRoots (r.den : ℤ)) =
      (((P.scaleRoots (r.den : ℤ)).eval r.num : ℤ) : ℝ) := by
    simp
  simpa [Polynomial.aeval_def] using h.symm.trans hev

lemma rational_small_polynomial_zero (P : ℤ[X]) (r : ℚ)
    (h : |aeval (r : ℝ) P| < 1 / (r.den : ℝ) ^ P.natDegree) :
    aeval (r : ℝ) P = 0 := by
  obtain ⟨z, hz⟩ := scaled_rational_eval_integer P r
  have hd : 0 < (r.den : ℝ) ^ P.natDegree := by
    have : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
    positivity
  have hsmall : |(z : ℝ)| < 1 := by
    rw [← hz, abs_mul, abs_of_pos hd]
    have hh := (lt_div_iff₀ hd).mp h
    simpa [mul_comm] using hh
  have hsmallZ : |z| < (1 : ℤ) := by exact_mod_cast hsmall
  have hz0 : z = 0 := by
    have hh := abs_lt.mp hsmallZ
    omega
  rw [hz0, Int.cast_zero] at hz
  exact (mul_eq_zero.mp hz).resolve_left hd.ne'

lemma cast_aeval (P : ℤ[X]) (r : ℚ) :
    ((aeval r P : ℚ) : ℝ) = aeval (r : ℝ) P := by
  exact (Polynomial.aeval_algHom_apply ((Rat.castHom ℝ).toIntAlgHom) r P).symm

/-- Values must be small relative to the degree-dependent denominator bound.
Merely tending to zero is insufficient when polynomial degrees increase. -/
theorem irrational_of_monic_small_polynomials (x : ℝ)
    (hx : ∀ z : ℤ, (z : ℝ) ≠ x)
    (h : ∀ b : ℕ, 0 < b → ∃ P : ℤ[X], P.Monic ∧
      |aeval x P| < 1 / (b : ℝ) ^ P.natDegree) : Irrational x := by
  rintro ⟨r, rfl⟩
  obtain ⟨P, hP, hsmall⟩ := h r.den r.den_pos
  have hr := rational_small_polynomial_zero P r hsmall
  have hrQ : aeval r P = 0 := by
    apply Rat.cast_injective (α := ℝ)
    simpa [cast_aeval] using hr
  obtain ⟨z, hz, _⟩ := exists_integer_of_is_root_of_monic hP hrQ
  apply hx z
  exact_mod_cast hz.symm

end MonicPolynomialCriterion

#print axioms MonicPolynomialCriterion.scaled_rational_eval_integer
#print axioms MonicPolynomialCriterion.irrational_of_monic_small_polynomials
