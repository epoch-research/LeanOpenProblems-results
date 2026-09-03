import Submission.WeightedDenominatorSpecializationRigidity

/-! A rational rescaling defeats an apparent inert-at-five escape from the
quadratic-pole obstruction. This does not estimate unrestricted counts. -/
namespace Erdos322Research.WeightedInertDenominatorRigidity
noncomputable section
open Polynomial QuadraticQuarticFive WeightedDenominatorSpecializationRigidity
set_option Elab.async false
set_option maxHeartbeats 0

abbrev R := MvPolynomial (Fin 2) ℚ

private def coefficientScale (q : ℚ) : R →+* R :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun i => MvPolynomial.C q*MvPolynomial.X i)

@[simp] private lemma coefficientScale_C (q a : ℚ) :
    coefficientScale q (MvPolynomial.C a) = MvPolynomial.C a := by
  simp [coefficientScale]

@[simp] private lemma coefficientScale_X (q : ℚ) (i : Fin 2) :
    coefficientScale q (MvPolynomial.X i) = MvPolynomial.C q*MvPolynomial.X i := by
  simp [coefficientScale]

private def dilate (q r : ℚ) : Polynomial R →+* Polynomial R :=
  Polynomial.eval₂RingHom (Polynomial.C.comp (coefficientScale q))
    (Polynomial.C (MvPolynomial.C r)*Polynomial.X)

@[simp] private lemma dilate_C (q r : ℚ) (p : R) :
    dilate q r (C p) = C (coefficientScale q p) := by simp [dilate]

@[simp] private lemma dilate_X (q r : ℚ) :
    dilate q r X = C (MvPolynomial.C r)*X := by simp [dilate]

private lemma coefficientScale_inverse (p : R) :
    coefficientScale 5 (coefficientScale (1/5) p) = p := by
  have h : (coefficientScale 5).comp (coefficientScale (1/5)) = RingHom.id R := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro i
      simp only [RingHom.comp_apply, coefficientScale_X, map_mul, coefficientScale_C,
        RingHom.id_apply]
      rw [← mul_assoc, ← MvPolynomial.C_mul]
      norm_num
  exact congrArg (fun f : R →+* R => f p) h

private lemma dilate_inverse (p : Polynomial R) :
    dilate 5 25 (dilate (1/5) (1/25) p) = p := by
  have h : (dilate 5 25).comp (dilate (1/5) (1/25)) = RingHom.id (Polynomial R) := by
    apply Polynomial.ringHom_ext
    · intro p
      simp only [RingHom.comp_apply, dilate_C, coefficientScale_inverse, RingHom.id_apply]
    · simp only [RingHom.comp_apply, dilate_X, map_mul, dilate_C, coefficientScale_C,
        RingHom.id_apply]
      rw [← mul_assoc, ← Polynomial.C_mul, ← MvPolynomial.C_mul]
      norm_num
  exact congrArg (fun f : Polynomial R →+* Polynomial R => f p) h

/-- The proposed denominator, whose integral specializations have constant
term congruent to two modulo five. -/
def original : Polynomial R :=
  X^2+C (2+5*MvPolynomial.X 0^4+5*MvPolynomial.X 1^4)

private def transformedD : MvPolynomial (Fin 2) ℤ :=
  1250+5*MvPolynomial.X 0^4+5*MvPolynomial.X 1^4

private def transformed : Polynomial R :=
  X^2+C (MvPolynomial.map (Int.castRingHom ℚ) transformedD)

private lemma dilate_original :
    dilate (1/5) (1/25) original = C (MvPolynomial.C (1/625))*transformed := by
  simp [original, transformed, transformedD, map_ofNat]
  ring_nf; norm_num [← map_pow, ← map_mul]
  have hc : (C (MvPolynomial.C (1/625)) : Polynomial R)*1250 = 2 := by
    have hh : (C (MvPolynomial.C (1/625)) : Polynomial R)*C (MvPolynomial.C 1250) =
        C (MvPolynomial.C 2) := by
      rw [← map_mul, ← map_mul]
      norm_num
    simpa using hh
  rw [hc]
  try simp only [mul_comm]
  ring

private lemma dilate_transformed :
    dilate 5 25 transformed = C (MvPolynomial.C 625)*original := by
  simp [original, transformed, transformedD, map_ofNat]
  ring

private lemma transformed_good :
    GoodFive (MvPolynomial.eval (![1,0] : Fin 2 → ℤ) transformedD) := by
  have he : MvPolynomial.eval (![1,0] : Fin 2 → ℤ) transformedD = 1255 := by
    norm_num [transformedD]
  rw [he]
  exact Or.inr ⟨251, by norm_num, by norm_num⟩

/-- All-degree rigidity, despite the inert reduction of the original affine
quadratic denominator at every integral coefficient specialization. -/
theorem inert_affine_denominator_rigidity
    (a : ℚ) (m : ℕ) (P : Fin 4 → Polynomial R)
    (h : ∑ j, P j^4 = C (MvPolynomial.C a)*original^(4*m)) :
    ∃ b : Fin 4 → ℚ, ∀ j, P j = C (MvPolynomial.C (b j))*original^m := by
  have ht : ∑ j, (dilate (1/5) (1/25) (P j))^4 =
      C (MvPolynomial.C (a*(1/625)^(4*m)))*transformed^(4*m) := by
    have hh := congrArg (dilate (1/5) (1/25)) h
    simp only [map_sum, map_pow, map_mul, dilate_C, coefficientScale_C,
      dilate_original, mul_pow] at hh
    convert hh using 1
    simp only [map_mul, map_pow]
    ring
  obtain ⟨b, hb⟩ := rigidity_of_one_good_specialization transformedD
    (![1,0] : Fin 2 → ℤ) transformed_good (a*(1/625)^(4*m)) m
    (fun j => dilate (1/5) (1/25) (P j)) ht
  refine ⟨fun j => b j*625^m, ?_⟩
  intro j
  have hh := congrArg (dilate 5 25) (hb j)
  change dilate 5 25 (dilate (1/5) (1/25) (P j)) =
    dilate 5 25 (C (MvPolynomial.C (b j))*transformed^m) at hh
  rw [dilate_inverse] at hh
  simp only [map_mul, map_pow, dilate_C, coefficientScale_C, dilate_transformed,
    mul_pow] at hh
  convert hh using 1
  simp only [map_mul, map_pow]
  ring

end
end Erdos322Research.WeightedInertDenominatorRigidity
