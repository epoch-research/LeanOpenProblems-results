import Submission.MonicDenominatorFactor

/-! Positive monic binary-form divisor bounds without squarefreeness.
A single rationally irreducible factor controls the parameter count, so
repeated denominator factors need not have a derivative Bezout certificate. -/
namespace Erdos322Research.MonicBinaryDivisorBound

open Polynomial Finset PositiveBinaryFormBound PositiveBinaryFormCoercivity
open QuadraticBinaryFormBound MonicQuadraticFamilyBound MonicDenominatorFactor
set_option Elab.async false

lemma degree_at_least_two (f : ℤ[X]) (hf : f.Monic) (hd : 0 < f.natDegree)
    (hnoroot : ∀ t : ℝ, f.eval₂ (Int.castRingHom ℝ) t ≠ 0) :
    2 ≤ f.natDegree := by
  by_contra hh
  have he : f.natDegree=1 := by omega
  have hx := hf.eq_X_add_C he
  apply hnoroot (-(f.coeff 0 : ℝ))
  conv_lhs => rw [hx]
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_C,
    Int.coe_castRingHom, Polynomial.coeff_add, Polynomial.coeff_X_zero,
    Polynomial.coeff_C_zero, zero_add, neg_add_cancel]

/-- A monic rationally irreducible polynomial with no real zero gives a
subpolynomial divisor-fiber union, including degree two. -/
theorem irreducible_divisor_fibers_subpolynomial (f : ℤ[X]) (hf : f.Monic)
    (hd : 0 < f.natDegree) (hi : Irreducible (f.map (Int.castRingHom ℚ)))
    (hnoroot : ∀ t : ℝ, f.eval₂ (Int.castRingHom ℝ) t ≠ 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K > (0 : ℝ), ∀ (S : Finset (ℕ × ℕ)) (L : ℕ), 0 < L →
      (∀ a ∈ S, a.1.Coprime a.2) →
      (∀ a ∈ S, 0 < binaryValue f a.1 a.2) →
      (∀ a ∈ S, (binaryValue f a.1 a.2).toNat ∣ L) →
      (S.card : ℝ) ≤ K*(L : ℝ)^ε := by
  have hdeg := degree_at_least_two f hf hd hnoroot
  by_cases htwo : f.natDegree=2
  · obtain ⟨K,hK,hbound⟩ := quadratic_divisor_fibers_subpolynomial ε hε
    refine ⟨K,hK,?_⟩
    intro S L hL _hprim hpos hdvd
    apply hbound (f.coeff 1) (f.coeff 0)
      (negative_discriminant f hf htwo hnoroot) S L hL
    · intro a ha
      simpa only [binaryValue_quadratic f hf htwo] using hpos a ha
    · intro a ha
      simpa only [binaryValue_quadratic f hf htwo] using hdvd a ha
  · have hd3 : 3 ≤ f.natDegree := by omega
    obtain ⟨U,V,D,hD,hder⟩ := irreducible_derivative_certificate f hi
    obtain ⟨H,_hH,hheight⟩ := exists_coercivity f hf hd hnoroot
    obtain ⟨K,hK,hbound⟩ := primitive_divisor_fibers_subpolynomial
      f U V hf hd3 D H hD hder ε hε
    refine ⟨K,hK,?_⟩
    intro S L hL hprim hpos hdvd
    apply hbound S L hL hprim hpos hdvd
    intro a ha
    have he : (binaryValue f a.1 a.2).natAbs=(binaryValue f a.1 a.2).toNat := by
      have hz := (Int.natAbs_of_nonneg (hpos a ha).le).trans
        (Int.toNat_of_nonneg (hpos a ha).le).symm
      exact_mod_cast hz
    simpa only [he] using hheight a.1 a.2

/-- The entire positive-value divisor-fiber union for any fixed nonconstant
monic polynomial with no real zero is subpolynomial. Repeated factors are
allowed, and no explicit derivative certificate is assumed. -/
theorem monic_divisor_fibers_subpolynomial (f : ℤ[X]) (hf : f.Monic)
    (hd : 0 < f.natDegree)
    (hnoroot : ∀ t : ℝ, f.eval₂ (Int.castRingHom ℝ) t ≠ 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K > (0 : ℝ), ∀ (S : Finset (ℕ × ℕ)) (L : ℕ), 0 < L →
      (∀ a ∈ S, a.1.Coprime a.2) →
      (∀ a ∈ S, 0 < a.2) →
      (∀ a ∈ S, (binaryValue f a.1 a.2).toNat ∣ L) →
      (S.card : ℝ) ≤ K*(L : ℝ)^ε := by
  obtain ⟨h,hh,hdh,hhf,hi⟩ := exists_monic_rational_irreducible_factor f hf hd
  obtain ⟨q,hq⟩ := hhf
  have hq0 : q ≠ 0 := by intro hz; rw [hz,mul_zero] at hq; exact hf.ne_zero hq
  have hhnoroot (t : ℝ) : h.eval₂ (Int.castRingHom ℝ) t ≠ 0 := by
    intro ht
    apply hnoroot t
    rw [hq,Polynomial.eval₂_mul,ht,zero_mul]
  obtain ⟨K,hK,hbound⟩ := irreducible_divisor_fibers_subpolynomial
    h hh hdh hi hhnoroot ε hε
  refine ⟨K,hK,?_⟩
  intro S L hL hprim hbpos hdvd
  have hhpos (a : ℕ × ℕ) (ha : a ∈ S) : 0 < binaryValue h a.1 a.2 :=
    binaryValue_positive h hh hhnoroot a.1 a.2 (by have := hbpos a ha; omega)
  have hfpos (a : ℕ × ℕ) (ha : a ∈ S) : 0 < binaryValue f a.1 a.2 :=
    binaryValue_positive f hf hnoroot a.1 a.2 (by have := hbpos a ha; omega)
  apply hbound S L hL hprim hhpos
  intro a ha
  have hdZ : binaryValue h a.1 a.2 ∣ binaryValue f a.1 a.2 := by
    refine ⟨binaryValue q a.1 a.2,?_⟩
    rw [hq,binaryValue_mul h q hh.ne_zero hq0 a.1 a.2 (hbpos a ha)]
  have hdN : (binaryValue h a.1 a.2).toNat ∣ (binaryValue f a.1 a.2).toNat := by
    apply Int.natCast_dvd_natCast.mp
    simpa only [Int.toNat_of_nonneg (hhpos a ha).le,
      Int.toNat_of_nonneg (hfpos a ha).le] using hdZ
  exact hdN.trans (hdvd a ha)

end Erdos322Research.MonicBinaryDivisorBound
