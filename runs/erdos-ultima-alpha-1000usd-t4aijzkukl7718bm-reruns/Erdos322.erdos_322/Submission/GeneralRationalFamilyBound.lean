import Submission.NonmonicDenominatorCancellation

/-! Nonmonic and repeated denominators in fixed rational-family bounds.
All rational parameters here are nonnegative and represented by primitive
pairs with positive denominator. These statements do not bound varying
families or the unrestricted power-sum representation count. -/
namespace Erdos322Research.GeneralRationalFamilyBound

open Polynomial Finset PositiveBinaryFormBound PositiveBinaryFormCoercivity
open NormalizedBinaryFormBound NonmonicDenominatorCancellation
set_option Elab.async false

lemma binaryValue_ne_zero (f : ℤ[X])
    (hnoroot : ∀ t : ℝ, f.eval₂ (Int.castRingHom ℝ) t ≠ 0)
    (a b : ℕ) (hb : 0 < b) : binaryValue f a b ≠ 0 := by
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  have hh := realValue_ratio f ((a : ℝ)/b) (a : ℝ) (b : ℝ)
    (div_mul_cancel₀ (a : ℝ) hb0)
  rw [realValue_nat] at hh
  intro hz
  rw [hz,Int.cast_zero] at hh
  exact (mul_ne_zero (pow_ne_zero _ hb0) (hnoroot _)) hh.symm

/-- Fixed reduced rational families with a nonconstant denominator having
no real zero have subpolynomial parameter counts at integral scale.
There is no monicity, squarefreeness or numerator-degree assumption. -/
theorem rational_family_bound {ι : Type*} [Fintype ι]
    (f B : ℤ[X]) (g A : ι → ℤ[X]) (C : ℕ)
    (hd : 0 < f.natDegree) (hC : 0 < C)
    (hnoroot : ∀ t : ℝ, f.eval₂ (Int.castRingHom ℝ) t ≠ 0)
    (hbez : (∑ i, A i*g i)+B*f=Polynomial.C (C : ℤ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K > (0 : ℝ), ∀ (S : Finset (ℕ × ℕ)) (L : ℕ), 0 < L →
      (∀ a ∈ S, a.1.Coprime a.2) →
      (∀ a ∈ S, 0 < a.2) →
      (∀ a ∈ S, ∀ i, ∃ z : ℤ,
        (L : ℚ)*(g i).eval₂ (Int.castRingHom ℚ) ((a.1 : ℚ)/a.2) /
          f.eval₂ (Int.castRingHom ℚ) ((a.1 : ℚ)/a.2) = z) →
      (S.card : ℝ) ≤ K*(L : ℝ)^ε := by
  have hf : f ≠ 0 := by intro hz; simp [hz] at hd
  have hAp : 0 < f.leadingCoeff.natAbs := Int.natAbs_pos.mpr (leadingCoeff_ne_zero.mpr hf)
  let M : ℕ := C*f.leadingCoeff.natAbs^(certificateDegree f B A)
  have hMp : 0 < M := mul_pos hC (pow_pos hAp _)
  obtain ⟨K,hK,hbound⟩ := divisor_fibers_subpolynomial f hd hnoroot ε hε
  refine ⟨K*(M : ℝ)^ε, by positivity, ?_⟩
  intro S L hL hprim hbpos hint
  have hdvd (a : ℕ × ℕ) (ha : a ∈ S) : (binaryValue f a.1 a.2).natAbs ∣ M*L :=
    NonmonicDenominatorCancellation.denominator_dvd_fixed_multiple f B g A C hC hbez
      (hbpos a ha) hL (hprim a ha) (binaryValue_ne_zero f hnoroot a.1 a.2 (hbpos a ha))
      (hint a ha)
  have hb := hbound S (M*L) (mul_pos hMp hL) hprim hbpos hdvd
  simpa only [Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg M) (Nat.cast_nonneg L), mul_assoc] using hb

/-- In every positive even-power norm family the no-real-pole condition
follows from the norm identity and reducedness certificate. -/
theorem even_rational_family_bound {ι : Type*} [Fintype ι]
    (f B : ℤ[X]) (g A : ι → ℤ[X]) (C : ℕ) (N : ℤ)
    (m : ℕ) (hm : 0 < m) (hd : 0 < f.natDegree) (hC : 0 < C)
    (hbez : (∑ i, A i*g i)+B*f=Polynomial.C (C : ℤ))
    (hnorm : ∑ i, g i^(2*m)=Polynomial.C N*f^(2*m))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K > (0 : ℝ), ∀ (S : Finset (ℕ × ℕ)) (L : ℕ), 0 < L →
      (∀ a ∈ S, a.1.Coprime a.2) →
      (∀ a ∈ S, 0 < a.2) →
      (∀ a ∈ S, ∀ i, ∃ z : ℤ,
        (L : ℚ)*(g i).eval₂ (Int.castRingHom ℚ) ((a.1 : ℚ)/a.2) /
          f.eval₂ (Int.castRingHom ℚ) ((a.1 : ℚ)/a.2) = z) →
      (S.card : ℝ) ≤ K*(L : ℝ)^ε := by
  apply rational_family_bound f B g A C hd hC
    (EvenPolynomialNormDegree.denominator_no_real_zero f B g A C N m hm hC hnorm hbez)
    hbez ε hε

end Erdos322Research.GeneralRationalFamilyBound
