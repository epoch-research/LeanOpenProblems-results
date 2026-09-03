import Submission.MonicBinaryDivisorBound

/-! Fixed even-power rational families with arbitrary nonconstant monic
integer denominators. Repeated factors are allowed; no derivative certificate
or degree restriction is required beyond nonconstancy. This is not an
unrestricted representation-count theorem. -/
namespace Erdos322Research.MonicEvenRationalFamilyBound

open Polynomial Finset PositiveBinaryFormBound RationalCurveDenominatorBound
open PositiveBinaryFormCoercivity MonicBinaryDivisorBound
set_option Elab.async false

/-- For a fixed reduced monic even-power rational family, all primitive
nonnegative parameter pairs giving integral coordinates at scale L have
subpolynomial count. Repeated denominator factors and degree two are allowed. -/
theorem monic_even_rational_family_bound {ι : Type*} [Fintype ι]
    (f B : ℤ[X]) (g A : ι → ℤ[X]) (C : ℕ) (N : ℤ)
    (m : ℕ) (hm : 0 < m) (hf : f.Monic) (hd : 0 < f.natDegree) (hC : 0 < C)
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
  obtain ⟨K,hK,hbound⟩ := monic_divisor_fibers_subpolynomial f hf hd hnoroot ε hε
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
  have hb := hbound S (C*L) (mul_pos hC hL) hprim hbpos hdvd
  simpa only [Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg C) (Nat.cast_nonneg L), mul_assoc] using hb

end Erdos322Research.MonicEvenRationalFamilyBound
