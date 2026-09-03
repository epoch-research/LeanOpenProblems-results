import Submission.PositiveBinaryFormCoercivity
import Submission.EvenPolynomialNormDegree

/-! A fixed-family denominator bound for every positive even exponent.
Numerator-degree, positivity and coercivity hypotheses are consequences of
the norm identity and the displayed coprimality certificate. This is not a
bound on all integer representations or on a varying collection of families. -/
namespace Erdos322Research.EvenRationalFamilyBound

open Polynomial Finset PositiveBinaryFormBound RationalCurveDenominatorBound
open PositiveBinaryFormCoercivity
set_option Elab.async false

/-- Primitive nonnegative rational parameters in any fixed certified monic
family have a subpolynomial count at a common integral scale. -/
theorem even_rational_family_bound {ι : Type*} [Fintype ι]
    (f U V B : ℤ[X]) (g A : ι → ℤ[X]) (D C : ℕ) (N : ℤ)
    (m : ℕ) (hm : 0 < m)
    (hf : f.Monic) (hd : 3 ≤ f.natDegree) (hD : 0 < D) (hC : 0 < C)
    (hder : U*f+V*f.derivative = Polynomial.C (D : ℤ))
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
  obtain ⟨H,hH,hheight⟩ := exists_coercivity f hf (by omega) hnoroot
  obtain ⟨K,hK,hbound⟩ := rational_parameter_bound f U V B g A D C H hf hd hD hC
    hdeg hder hbez ε hε
  refine ⟨K,hK,?_⟩
  intro S L hL hprim hbpos hint
  have hpos (a : ℕ × ℕ) (ha : a ∈ S) : 0 < binaryValue f a.1 a.2 :=
    binaryValue_positive f hf hnoroot a.1 a.2 (by have := hbpos a ha; omega)
  apply hbound S L hL hprim hbpos hpos hint
  intro a ha
  have he : (binaryValue f a.1 a.2).natAbs=(binaryValue f a.1 a.2).toNat := by
    have hz := (Int.natAbs_of_nonneg (hpos a ha).le).trans
      (Int.toNat_of_nonneg (hpos a ha).le).symm
    exact_mod_cast hz
  simpa only [he] using hheight a.1 a.2

/-- In particular, the quartic-family theorem needs no separate numerator
 degree assumption. -/
theorem quartic_rational_family_bound {ι : Type*} [Fintype ι]
    (f U V B : ℤ[X]) (g A : ι → ℤ[X]) (D C : ℕ) (N : ℤ)
    (hf : f.Monic) (hd : 3 ≤ f.natDegree) (hD : 0 < D) (hC : 0 < C)
    (hder : U*f+V*f.derivative = Polynomial.C (D : ℤ))
    (hbez : (∑ i, A i*g i)+B*f = Polynomial.C (C : ℤ))
    (hnorm : ∑ i, g i^4=Polynomial.C N*f^4)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K > (0 : ℝ), ∀ (S : Finset (ℕ × ℕ)) (L : ℕ), 0 < L →
      (∀ a ∈ S, a.1.Coprime a.2) →
      (∀ a ∈ S, 0 < a.2) →
      (∀ a ∈ S, ∀ i, ∃ z : ℤ,
        (L : ℚ)*(g i).eval₂ (Int.castRingHom ℚ) ((a.1 : ℚ)/a.2) /
          f.eval₂ (Int.castRingHom ℚ) ((a.1 : ℚ)/a.2) = z) →
      (S.card : ℝ) ≤ K*(L : ℝ)^ε := by
  exact even_rational_family_bound f U V B g A D C N 2 (by norm_num)
    hf hd hD hC hder hbez hnorm ε hε

end Erdos322Research.EvenRationalFamilyBound
