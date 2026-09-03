import Submission.QuadraticBinaryFormBound
import Submission.EvenRationalFamilyBound

/-! The previously excluded degree-two monic denominators also give
subpolynomial fixed-family counts. Completing the square avoids any separate
derivative Bezout or coercivity hypothesis in this case. -/
namespace Erdos322Research.MonicQuadraticFamilyBound

open Polynomial Finset PositiveBinaryFormBound RationalCurveDenominatorBound
open PositiveBinaryFormCoercivity QuadraticBinaryFormBound
set_option Elab.async false

lemma binaryValue_quadratic (f : ℤ[X]) (hf : f.Monic) (hd : f.natDegree=2)
    (a b : ℕ) : binaryValue f a b=quadraticValue (f.coeff 1) (f.coeff 0) a b := by
  have hc : f.coeff 2=1 := by simpa only [hd] using hf.coeff_natDegree
  simp only [binaryValue,hd]
  norm_num [Finset.sum_range_succ,hc,quadraticValue]
  ring

lemma eval_quadratic (f : ℤ[X]) (hf : f.Monic) (hd : f.natDegree=2) (t : ℝ) :
    f.eval₂ (Int.castRingHom ℝ) t = t^2+(f.coeff 1 : ℝ)*t+(f.coeff 0 : ℝ) := by
  have hc : f.coeff 2=1 := by simpa only [hd] using hf.coeff_natDegree
  rw [Polynomial.eval₂_eq_sum_range' _ (show f.natDegree < 3 by omega)]
  norm_num [Finset.sum_range_succ,hc]
  ring

lemma negative_discriminant (f : ℤ[X]) (hf : f.Monic) (hd : f.natDegree=2)
    (hnoroot : ∀ t : ℝ, f.eval₂ (Int.castRingHom ℝ) t ≠ 0) :
    0 < 4*f.coeff 0-(f.coeff 1)^2 := by
  by_contra hnot
  have hnonneg : (0 : ℝ) ≤ (f.coeff 1 : ℝ)^2-4*(f.coeff 0 : ℝ) := by
    have hz : (f.coeff 1)^2-4*f.coeff 0 ≥ 0 := by omega
    exact_mod_cast hz
  have hs := Real.sq_sqrt hnonneg
  obtain ⟨t,ht⟩ := exists_quadratic_eq_zero (a := (1 : ℝ))
    (b := (f.coeff 1 : ℝ)) (c := (f.coeff 0 : ℝ)) (by norm_num)
    ⟨Real.sqrt ((f.coeff 1 : ℝ)^2-4*(f.coeff 0 : ℝ)), by
      simp only [discrim, mul_one]
      nlinarith [hs]⟩
  apply hnoroot t
  rw [eval_quadratic f hf hd]
  nlinarith [ht]

/-- Every fixed reduced monic quadratic-denominator even-power family has
subpolynomially many primitive nonnegative parameters at integral scale L.
No derivative certificate or numerator-degree bound is assumed. -/
theorem quadratic_even_rational_family_bound {ι : Type*} [Fintype ι]
    (f B : ℤ[X]) (g A : ι → ℤ[X]) (C : ℕ) (N : ℤ)
    (m : ℕ) (hm : 0 < m) (hf : f.Monic) (hd : f.natDegree=2) (hC : 0 < C)
    (hbez : (∑ i, A i*g i)+B*f = Polynomial.C (C : ℤ))
    (hnorm : ∑ i, g i^(2*m)=Polynomial.C N*f^(2*m))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K > (0 : ℝ), ∀ (S : Finset (ℕ × ℕ)) (L : ℕ), 0 < L →
      (∀ a ∈ S, a.1.Coprime a.2) →
      (∀ a ∈ S, 0 < a.2) →
      (∀ a ∈ S, ∀ i, ∃ z : ℤ,
        (L : ℚ)*(g i).eval₂ (Int.castRingHom ℚ) ((a.1 : ℚ)/a.2) /
          f.eval₂ (Int.castRingHom ℚ) ((a.1 : ℚ)/a.2) = z) →
      (S.card : ℝ) ≤ K*(L : ℝ)^ε := by
  have hnoroot := EvenPolynomialNormDegree.denominator_no_real_zero
    f B g A C N m hm hC hnorm hbez
  have hdeg := EvenPolynomialNormDegree.numerator_degree_le f g N m hm hnorm
  have hdisc := negative_discriminant f hf hd hnoroot
  obtain ⟨K,hK,hbound⟩ := quadratic_divisor_fibers_subpolynomial ε hε
  refine ⟨K*(C : ℝ)^ε, by positivity, ?_⟩
  intro S L hL hprim hbpos hint
  have hpos (a : ℕ × ℕ) (ha : a ∈ S) : 0 < binaryValue f a.1 a.2 :=
    binaryValue_positive f hf hnoroot a.1 a.2 (by have := hbpos a ha; omega)
  have hdvd (a : ℕ × ℕ) (ha : a ∈ S) : (binaryValue f a.1 a.2).toNat ∣ C*L := by
    have hn : 0 < (binaryValue f a.1 a.2).toNat := by have := hpos a ha; omega
    have hval := (Int.toNat_of_nonneg (hpos a ha).le).symm
    apply denominator_dvd_fixed_multiple f B g A C hf hbez hn (hprim a ha) hval
    intro i
    exact integer_scaled_value_implies_divisibility f (g i) hf (hdeg i)
      (hbpos a ha) hn (hprim a ha) hval (hint a ha i)
  have hb := hbound (f.coeff 1) (f.coeff 0) hdisc S (C*L) (mul_pos hC hL)
    (by intro a ha; simpa only [binaryValue_quadratic f hf hd] using hpos a ha)
    (by intro a ha; simpa only [binaryValue_quadratic f hf hd] using hdvd a ha)
  simpa only [Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg C) (Nat.cast_nonneg L), mul_assoc] using hb

end Erdos322Research.MonicQuadraticFamilyBound
