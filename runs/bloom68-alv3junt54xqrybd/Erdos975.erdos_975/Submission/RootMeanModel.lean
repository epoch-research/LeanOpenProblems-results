/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
import Submission.RootMeanNumberField

/-!
# An unconditional ideal coefficient model for monic irreducible polynomials

Every monic irreducible integer polynomial has a number-field ideal coefficient
sequence with a strictly positive linear mean and with the same prime
coefficients outside a finite conductor exceptional set. The field is actually
constructed as `AdjoinRoot (f.map (Int.castRingHom ℚ))`. The conductor exponent
is proved positive using the nonzero, integral power-basis discriminant.

This is a first-order coefficient model, not the polynomial root-mean theorem:
agreement at good primes alone does not imply agreement of means.

The discriminant-to-conductor argument adapts just the needed bridge from
`/opt/tauceti/TauCeti/NumberTheory/NumberField/Quadratic/Splitting.lean`,
`algebraMap_four_mul_mem_conductor`, removing its quadratic specialization.
The discriminant and Kummer–Dedekind results themselves are from Mathlib.
-/

namespace Erdos975Support

open Filter Polynomial NumberField Ideal
open scoped Topology

/-- A generating algebraic integer has a nonzero integer in its conductor.
This is obtained from the integral, nonzero discriminant of its rational power
basis, rather than assuming that its order has finite index. -/
theorem exists_nonzero_integer_mem_conductor {K : Type*} [Field K] [NumberField K]
    (θ : 𝓞 K) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    ∃ D : ℤ, D ≠ 0 ∧ (algebraMap ℤ (𝓞 K)) D ∈ conductor ℤ θ := by
  classical
  have hint : IsIntegral ℤ (θ : K) := θ.isIntegral_coe
  have hintQ : IsIntegral ℚ (θ : K) := hint.tower_top
  let pb : PowerBasis ℚ K := PowerBasis.ofAdjoinEqTop' hintQ hgen
  have hpbgen : pb.gen = (θ : K) := PowerBasis.ofAdjoinEqTop'_gen hintQ hgen
  have hintdiscr : IsIntegral ℤ (Algebra.discr ℚ pb.basis) := by
    apply Algebra.discr_isIntegral
    intro i
    rw [pb.basis_eq_pow, hpbgen]
    exact hint.pow i.val
  obtain ⟨D, hD⟩ := IsIntegrallyClosed.isIntegral_iff.mp hintdiscr
  have hD0 : D ≠ 0 := by
    intro hz
    have hd0 := Algebra.discr_not_zero_of_basis ℚ pb.basis
    apply hd0
    rw [← hD, hz, map_zero]
  refine ⟨D, hD0, ?_⟩
  rw [mem_conductor_iff]
  intro b
  have key := Algebra.discr_mul_isIntegral_mem_adjoin (R := ℤ) (K := ℚ) (L := K)
    (B := pb) (hpbgen ▸ hint) (z := (b : K)) b.isIntegral_coe
  rw [← hD, hpbgen] at key
  let φ : (𝓞 K) →ₐ[ℤ] K := IsScalarTower.toAlgHom ℤ (𝓞 K) K
  have hmap : (Algebra.adjoin ℤ {θ}).map φ = Algebra.adjoin ℤ {(θ : K)} := by
    rw [← Algebra.adjoin_image, Set.image_singleton]
    rfl
  have himg : (algebraMap ℤ ℚ D) • (b : K) = φ ((algebraMap ℤ (𝓞 K) D) * b) := by
    rw [map_mul, IsScalarTower.coe_toAlgHom',
      ← IsScalarTower.algebraMap_apply ℤ (𝓞 K) K, Algebra.smul_def]
    simp
  rw [himg, ← hmap] at key
  obtain ⟨y, hy, hyeq⟩ := key
  rwa [(FaithfulSMul.algebraMap_injective (𝓞 K) K) hyeq] at hy

/-- Consequently the conductor exponent is positive for a rational generator. -/
theorem exponent_pos_of_generator {K : Type*} [Field K] [NumberField K]
    (θ : 𝓞 K) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    0 < RingOfIntegers.exponent θ := by
  obtain ⟨D, hD0, hD⟩ := exists_nonzero_integer_mem_conductor θ hgen
  have hne : under ℤ (conductor ℤ θ) ≠ ⊥ := by
    intro hbot
    have hm : D ∈ under ℤ (conductor ℤ θ) := Ideal.mem_comap.mpr hD
    rw [hbot, Ideal.mem_bot] at hm
    exact hD0 hm
  exact Nat.pos_of_ne_zero ((Ideal.absNorm_eq_zero_iff.not).mpr hne)

/-- For every monic irreducible integer polynomial, an actual ideal coefficient
model has a positive linear mean and agrees with its root counts at all primes
outside one nonzero modulus. This does not identify the root-count mean. -/
theorem exists_ideal_prime_model_of_monic_irreducible (f : ℤ[X]) (hf : Irreducible f)
    (hmonic : f.Monic) :
    ∃ D > 0, ∃ a : ArithmeticFunction ℝ, ∃ κ > (0 : ℝ),
      Tendsto (fun N : ℕ ↦ arithmeticSummatory a N / (N : ℝ)) atTop (𝓝 κ) ∧
        ∀ p : ℕ, p.Prime → ¬ p ∣ D → polynomialRootCoefficients f p = a p := by
  classical
  let F := f.map (Int.castRingHom ℚ)
  have hFirr : Irreducible F := (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hmonic.isPrimitive).mp hf
  have hFmonic : F.Monic := hmonic.map _
  letI : Fact (Irreducible F) := ⟨hFirr⟩
  let K := AdjoinRoot F
  letI : Field K := AdjoinRoot.instField
  let pb : PowerBasis ℚ K := AdjoinRoot.powerBasis hFirr.ne_zero
  letI : FiniteDimensional ℚ K := pb.finite
  letI : NumberField K := ⟨⟩
  let α : K := AdjoinRoot.root F
  have hαf : aeval α f = 0 := by
    rw [aeval_def, algebraMap_int_eq]
    have hcomp : (AdjoinRoot.of F).comp (Int.castRingHom ℚ) = Int.castRingHom K :=
      RingHom.ext_int _ _
    rw [← hcomp, ← eval₂_map]
    exact AdjoinRoot.eval₂_root F
  have hα : IsIntegral ℤ α := ⟨f, hmonic, hαf⟩
  let θ : 𝓞 K := ⟨α, hα⟩
  have hminQ : minpoly ℚ (θ : K) = F := by
    change minpoly ℚ (AdjoinRoot.root F) = F
    rw [AdjoinRoot.minpoly_root hFirr.ne_zero, hFmonic.leadingCoeff, inv_one, C_1, mul_one]
  have hmin : minpoly ℤ θ = f := by
    apply Polynomial.map_injective (Int.castRingHom ℚ) (Int.cast_injective)
    have he := minpoly.isIntegrallyClosed_eq_field_fractions ℚ K θ.isIntegral
    rw [hminQ] at he
    exact he.symm
  have hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤ := by
    simpa only [pb, AdjoinRoot.powerBasis_gen] using pb.adjoin_gen_eq_top
  refine ⟨RingOfIntegers.exponent θ, exponent_pos_of_generator θ hgen,
    idealNormCoefficients K, dedekindZeta_residue K, dedekindZeta_residue_pos K,
    tendsto_idealNormCoefficients_mean K, ?_⟩
  intro p hp hpD
  letI : Fact p.Prime := ⟨hp⟩
  rw [← hmin]
  exact polynomialRootCoefficients_minpoly_prime K θ p hpD

end Erdos975Support
