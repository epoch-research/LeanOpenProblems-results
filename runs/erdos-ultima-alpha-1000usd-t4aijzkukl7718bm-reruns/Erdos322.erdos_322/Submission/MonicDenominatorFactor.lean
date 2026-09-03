import Submission.MonicQuadraticFamilyBound

/-! Monic irreducible denominator factors and integer Bezout certificates.
These lemmas will be used to remove repeated-factor restrictions from fixed
rational-family counting bounds. -/
namespace Erdos322Research.MonicDenominatorFactor

open Polynomial Finset PositiveBinaryFormBound RationalCurveDenominatorBound
open scoped nonZeroDivisors
set_option Elab.async false

/-- A nonconstant monic integer polynomial has a monic integer divisor which
is irreducible over the rationals. -/
theorem exists_monic_rational_irreducible_factor (f : ℤ[X]) (hf : f.Monic)
    (hd : 0 < f.natDegree) :
    ∃ h : ℤ[X], h.Monic ∧ 0 < h.natDegree ∧ h ∣ f ∧
      Irreducible (h.map (Int.castRingHom ℚ)) := by
  have hdf : 0 < (f.map (algebraMap ℤ ℚ)).natDegree := by rwa [hf.natDegree_map]
  obtain ⟨q,hq,hqi,hqf⟩ := exists_monic_irreducible_factor (f.map (algebraMap ℤ ℚ))
    (not_isUnit_of_natDegree_pos _ hdf)
  obtain ⟨h,hh⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd ℚ hf hqf
  rw [hq.leadingCoeff, C_1, mul_one] at hh
  have hm : h.Monic := by
    apply (Function.Injective.monic_map_iff (f := algebraMap ℤ ℚ)
      (IsFractionRing.injective ℤ ℚ)).mpr
    rwa [hh]
  have hi : Irreducible (h.map (algebraMap ℤ ℚ)) := hh ▸ hqi
  have hp : 0 < h.natDegree :=
    hm.natDegree_pos_of_not_isUnit ((hm.irreducible_iff_irreducible_map_fraction_map).mpr hi).not_isUnit
  refine ⟨h,hm,hp,?_,?_⟩
  · apply (hf.dvd_iff_fraction_map_dvd_fraction_map (K := ℚ) hm).mp
    rwa [hh]
  · exact hi

/-- A rational Bezout identity between integer polynomials can be cleared to
one with a strictly positive integer constant. -/
theorem positive_integer_bezout (f g : ℤ[X])
    (hcop : IsCoprime (f.map (Int.castRingHom ℚ)) (g.map (Int.castRingHom ℚ))) :
    ∃ (U V : ℤ[X]) (D : ℕ), 0 < D ∧ U*f+V*g=Polynomial.C (D : ℤ) := by
  classical
  obtain ⟨u,v,huv⟩ := hcop
  let u₀ : ℤ[X] := IsLocalization.integerNormalization (ℤ⁰) u
  let v₀ : ℤ[X] := IsLocalization.integerNormalization (ℤ⁰) v
  obtain ⟨c,hc⟩ := IsLocalization.integerNormalization_map_to_map (ℤ⁰) u
  obtain ⟨d,hd⟩ := IsLocalization.integerNormalization_map_to_map (ℤ⁰) v
  have hc0 : (c : ℤ) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp c.property
  have hd0 : (d : ℤ) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp d.property
  have hu : u₀.map (Int.castRingHom ℚ)=Polynomial.C (c : ℚ)*u := by
    simpa [u₀,Algebra.smul_def] using hc
  have hv : v₀.map (Int.castRingHom ℚ)=Polynomial.C (d : ℚ)*v := by
    simpa [v₀,Algebra.smul_def] using hd
  let D : ℕ := ((c : ℤ)*(d : ℤ)).natAbs^2
  have hD : 0 < D := pow_pos (Int.natAbs_pos.mpr (mul_ne_zero hc0 hd0)) 2
  have hDc : (D : ℤ)=((c : ℤ)*(d : ℤ))^2 := by
    dsimp [D]
    rw [Int.natCast_natAbs,sq_abs]
  refine ⟨Polynomial.C ((c : ℤ)*(d : ℤ)^2)*u₀,
    Polynomial.C ((c : ℤ)^2*(d : ℤ))*v₀,D,hD,?_⟩
  apply Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  simp only [Polynomial.map_add,Polynomial.map_mul,Polynomial.map_C,hu,hv]
  have hDq : (D : ℚ)=((c : ℚ)*(d : ℚ))^2 := by exact_mod_cast hDc
  simp only [Int.coe_castRingHom,Int.cast_mul,Int.cast_pow,Int.cast_natCast]
  rw [hDq]
  calc
    _ = Polynomial.C (((c : ℚ)*(d : ℚ))^2)*
        (u*f.map (Int.castRingHom ℚ)+v*g.map (Int.castRingHom ℚ)) := by
      simp only [Polynomial.C_mul,Polynomial.C_pow]
      ring
    _ = _ := by rw [huv,mul_one]

/-- Every rationally irreducible integer polynomial admits the positive
integer derivative certificate used by the modular root bound. -/
theorem irreducible_derivative_certificate (h : ℤ[X])
    (hi : Irreducible (h.map (Int.castRingHom ℚ))) :
    ∃ (U V : ℤ[X]) (D : ℕ), 0 < D ∧ U*h+V*h.derivative=Polynomial.C (D : ℤ) := by
  apply positive_integer_bezout h h.derivative
  simpa only [Polynomial.Separable,Polynomial.derivative_map] using hi.separable

/-- Homogenization is multiplicative at parameters with positive second
coordinate. -/
theorem binaryValue_mul (f g : ℤ[X]) (hf : f ≠ 0) (hg : g ≠ 0)
    (a b : ℕ) (hb : 0 < b) :
    binaryValue (f*g) a b=binaryValue f a b*binaryValue g a b := by
  apply Int.cast_injective (α := ℚ)
  rw [Int.cast_mul, binaryValue_cast_ratio _ a b hb,
    binaryValue_cast_ratio _ a b hb, binaryValue_cast_ratio _ a b hb]
  rw [Polynomial.natDegree_mul hf hg, pow_add, Polynomial.eval₂_mul]
  ring

end Erdos322Research.MonicDenominatorFactor
