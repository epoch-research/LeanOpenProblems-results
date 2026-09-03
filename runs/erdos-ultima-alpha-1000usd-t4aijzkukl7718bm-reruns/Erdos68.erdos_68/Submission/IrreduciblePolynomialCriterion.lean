import Submission.MonicPolynomialCriterion

/-! Irreducible auxiliary polynomials of degree at least two exclude rational
roots. No sufficiently small family for the conjectured sum is constructed. -/

namespace IrreduciblePolynomialCriterion

open Polynomial

lemma rational_eval_ne_zero (P : ℤ[X]) (hprim : P.IsPrimitive)
    (hirr : Irreducible P) (hdeg : 2 ≤ P.natDegree) (r : ℚ) : aeval r P ≠ 0 := by
  have hq : Irreducible (P.map (Int.castRingHom ℚ)) :=
    (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprim).mp hirr
  have hd : (P.map (Int.castRingHom ℚ)).natDegree ≠ 1 := by
    rw [natDegree_map_eq_of_injective (Int.cast_injective)]
    omega
  intro h
  apply hq.not_isRoot_of_natDegree_ne_one hd (x := r)
  simpa [IsRoot, eval_map, aeval_def] using h

theorem irrational_of_small_polynomials (x : ℝ)
    (h : ∀ b : ℕ, 0 < b → ∃ P : ℤ[X], P.IsPrimitive ∧ Irreducible P ∧
      2 ≤ P.natDegree ∧ |aeval x P| < 1 / (b : ℝ) ^ P.natDegree) :
    Irrational x := by
  rintro ⟨r, rfl⟩
  obtain ⟨P, hp, hi, hd, hs⟩ := h r.den r.den_pos
  have hr : aeval r P = 0 := by
    apply Rat.cast_injective (α := ℝ)
    simpa [MonicPolynomialCriterion.cast_aeval] using
      MonicPolynomialCriterion.rational_small_polynomial_zero P r hs
  exact rational_eval_ne_zero P hp hi hd r hr

lemma eisenstein_at_two (P : ℤ[X])
    (hl : ¬ (2 : ℤ) ∣ P.leadingCoeff)
    (hc : ∀ j < P.natDegree, (2 : ℤ) ∣ P.coeff j)
    (h0 : ¬ (4 : ℤ) ∣ P.coeff 0) :
    P.IsEisensteinAt (Ideal.span ({2} : Set ℤ)) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Ideal.mem_span_singleton] using hl
  · intro j hj
    exact Ideal.mem_span_singleton.mpr (hc j hj)
  · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    norm_num only [show (2 : ℤ)^2 = 4 by norm_num]
    exact h0

lemma rational_eval_ne_zero_of_mod_four (P : ℤ[X]) (hprim : P.IsPrimitive)
    (hdeg : 2 ≤ P.natDegree) (hl : ¬ (2 : ℤ) ∣ P.leadingCoeff)
    (hc : ∀ j < P.natDegree, (2 : ℤ) ∣ P.coeff j)
    (h0 : ¬ (4 : ℤ) ∣ P.coeff 0) (r : ℚ) : aeval r P ≠ 0 := by
  have hi : (Ideal.span ({2} : Set ℤ)).IsPrime := by
    apply (Ideal.span_singleton_prime (by norm_num : (2 : ℤ) ≠ 0)).mpr
    norm_num
  exact rational_eval_ne_zero P hprim
    ((eisenstein_at_two P hl hc h0).irreducible hi hprim (by omega)) hdeg r

theorem irrational_of_mod_four_small_polynomials (x : ℝ)
    (h : ∀ b : ℕ, 0 < b → ∃ P : ℤ[X], P.IsPrimitive ∧
      2 ≤ P.natDegree ∧ ¬ (2 : ℤ) ∣ P.leadingCoeff ∧
      (∀ j < P.natDegree, (2 : ℤ) ∣ P.coeff j) ∧
      ¬ (4 : ℤ) ∣ P.coeff 0 ∧
      |aeval x P| < 1 / (b : ℝ) ^ P.natDegree) : Irrational x := by
  rintro ⟨r, rfl⟩
  obtain ⟨P, hp, hd, hl, hc, h0, hs⟩ := h r.den r.den_pos
  have hr : aeval r P = 0 := by
    apply Rat.cast_injective (α := ℝ)
    simpa [MonicPolynomialCriterion.cast_aeval] using
      MonicPolynomialCriterion.rational_small_polynomial_zero P r hs
  exact rational_eval_ne_zero_of_mod_four P hp hd hl hc h0 r hr

end IrreduciblePolynomialCriterion

#print axioms IrreduciblePolynomialCriterion.rational_eval_ne_zero
#print axioms IrreduciblePolynomialCriterion.irrational_of_small_polynomials

#print axioms IrreduciblePolynomialCriterion.irrational_of_mod_four_small_polynomials
