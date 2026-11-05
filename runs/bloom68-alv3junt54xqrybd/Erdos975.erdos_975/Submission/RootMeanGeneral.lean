/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
import Submission.RootMeanMonic
import Submission.RootMeanNormalization
import Submission.LinearDivisorAverage

/-!
# Unconditional root-count means for all irreducible integer polynomials

Every nonconstant irreducible `f : ℤ[X]`, without a monicity or sign hypothesis,
has a strictly positive linear root-count mean. We construct the number field
of its monic integral normalization `g = f.integralNormalization` and an
integral generator with integer minimal polynomial `g`. At primes outside the
leading coefficient and the conductor, normalization and Kummer–Dedekind
identify the ORIGINAL coefficients `polynomialRootCoefficients f` with the
ideal-norm prime coefficients.

The prime-power bounds are also for `f`, not for `g`: its nonzero derivative
resultant gives an individual bound at every prime, and primitivity and
finite-modulus Hensel lifting give the degree bound at resultant-good primes.
The exceptional set is `range (f.leadingCoeff.natAbs + D + R.natAbs + 1)`.
The actual ideal Euler inverse has a finite local polynomial at every prime,
so `tendsto_summatory_of_idealEulerCorrection_of_degree` proves an absolutely
summable, strictly positive correction for `f` itself. We do NOT infer a mean
from finite-prime agreement with `g` or invert bad local root-count series.

For irreducible quadratics, this removes the mean premise from the existing
quadratic divisor-average reduction. The original eventual positivity premise
is retained for the inclusive floored sum. Combining the degree-one theorem
gives the original divisor-average conclusion RESTRICTED to natural degree at
most two. The balanced-divisor limit in degree at least three remains unproved;
no full-degree divisor-average theorem is claimed. No specification or original
Erdős theorem is imported.
-/

namespace Erdos975Support

open Filter Polynomial NumberField Ideal
open scoped Topology

/-- Every nonconstant irreducible integer polynomial has a strictly positive
linear root-count mean. Neither monicity nor a mean premise is required. -/
theorem exists_pos_rootMean_of_irreducible (f : ℤ[X]) (hf : Irreducible f)
    (hdeg : f.natDegree ≠ 0) :
    ∃ κ > (0 : ℝ), Tendsto (fun N : ℕ ↦
      rootCountSummatory (polynomialAbsValue f) N / (N : ℝ)) atTop (𝓝 κ) := by
  classical
  have hfprim : f.IsPrimitive := hf.isPrimitive hdeg
  -- Only the integral normalization is used to construct the ideal model.
  let g : ℤ[X] := f.integralNormalization
  have hgmonic : g.Monic := monic_integralNormalization hf.ne_zero
  have hgirr : Irreducible g :=
    integralNormalization_irreducible f hf (Nat.pos_of_ne_zero hdeg)
  let G := g.map (Int.castRingHom ℚ)
  have hGirr : Irreducible G :=
    (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
      hgmonic.isPrimitive).mp hgirr
  have hGmonic : G.Monic := hgmonic.map _
  letI : Fact (Irreducible G) := ⟨hGirr⟩
  let K := AdjoinRoot G
  letI : Field K := AdjoinRoot.instField
  let pb : PowerBasis ℚ K := AdjoinRoot.powerBasis hGirr.ne_zero
  letI : FiniteDimensional ℚ K := pb.finite
  letI : NumberField K := ⟨⟩
  let α : K := AdjoinRoot.root G
  have hαg : aeval α g = 0 := by
    rw [aeval_def, algebraMap_int_eq]
    have hcomp : (AdjoinRoot.of G).comp (Int.castRingHom ℚ) = Int.castRingHom K :=
      RingHom.ext_int _ _
    rw [← hcomp, ← eval₂_map]
    exact AdjoinRoot.eval₂_root G
  have hα : IsIntegral ℤ α := ⟨g, hgmonic, hαg⟩
  let θ : 𝓞 K := ⟨α, hα⟩
  have hminQ : minpoly ℚ (θ : K) = G := by
    change minpoly ℚ (AdjoinRoot.root G) = G
    rw [AdjoinRoot.minpoly_root hGirr.ne_zero, hGmonic.leadingCoeff,
      inv_one, C_1, mul_one]
  have hmin : minpoly ℤ θ = g := by
    apply Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
    have he := minpoly.isIntegrallyClosed_eq_field_fractions ℚ K θ.isIntegral
    rw [hminQ] at he
    exact he.symm
  have hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤ := by
    simpa only [pb, AdjoinRoot.powerBasis_gen] using pb.adjoin_gen_eq_top
  -- Include leading-coefficient, conductor, and ORIGINAL resultant bad primes.
  let A := f.leadingCoeff.natAbs
  have hA : 0 < A := Int.natAbs_pos.mpr (leadingCoeff_ne_zero.mpr hf.ne_zero)
  let D := RingOfIntegers.exponent θ
  have hD : 0 < D := exponent_pos_of_generator θ hgen
  let R : ℤ := f.resultant f.derivative
  have hR : R ≠ 0 := polynomial_resultant_derivative_ne_zero_of_irreducible f hf hdeg
  have hRabs : 0 < R.natAbs := Int.natAbs_pos.mpr hR
  let S : Finset ℕ := Finset.range (A + D + R.natAbs + 1)
  have houtside (p : ℕ) (hpS : p ∉ S) :
      ¬ (p : ℤ) ∣ f.leadingCoeff ∧ ¬ p ∣ D ∧ ¬ (p : ℤ) ∣ R := by
    have hlarge : A + D + R.natAbs + 1 ≤ p := by
      simpa only [S, Finset.mem_range, not_lt] using hpS
    refine ⟨?_, Nat.not_dvd_of_pos_of_lt hD (by omega), ?_⟩
    · rw [Int.natCast_dvd]
      exact Nat.not_dvd_of_pos_of_lt hA (by omega)
    · rw [Int.natCast_dvd]
      exact Nat.not_dvd_of_pos_of_lt hRabs (by omega)
  -- All transfer data below concern the actual root coefficients of f.
  have hrnonneg (n : ℕ) : 0 ≤ polynomialRootCoefficients f n := by
    change 0 ≤ (rootCount (polynomialAbsValue f) n : ℝ)
    exact Nat.cast_nonneg _
  have hrbounded (p : ℕ) (hp : p.Prime) :
      ∃ Cₚ : ℝ, ∀ k : ℕ, polynomialRootCoefficients f (p ^ k) ≤ Cₚ := by
    refine ⟨(p ^ (2 * padicValInt p R + 1) : ℕ), fun k ↦ ?_⟩
    change (rootCount (polynomialAbsValue f) (p ^ k) : ℝ) ≤ _
    exact_mod_cast rootCount_irreducible_polynomial_prime_pow_le_resultant_valuation
      f hf hdeg p hp k
  have hrgood (p : ℕ) (hp : p.Prime) (hpS : p ∉ S) (k : ℕ) (hk : 1 ≤ k) :
      polynomialRootCoefficients f (p ^ k) ≤ (f.natDegree : ℝ) := by
    have hs : PolynomialSimpleRootsMod f p :=
      polynomialSimpleRootsMod_of_not_dvd_resultant f (Nat.pos_of_ne_zero hdeg)
        p hp (houtside p hpS).2.2
    change (rootCount (polynomialAbsValue f) (p ^ k) : ℝ) ≤ (f.natDegree : ℝ)
    exact_mod_cast rootCount_polynomial_prime_pow_le f hfprim p hp hs k hk
  have hmatch (p : ℕ) (hp : p.Prime) (hpS : p ∉ S) :
      polynomialRootCoefficients f p = idealNormCoefficients K p := by
    letI : Fact p.Prime := ⟨hp⟩
    have hfg : polynomialRootCoefficients f p = polynomialRootCoefficients g p := by
      change (rootCount (polynomialAbsValue f) p : ℝ) =
        (rootCount (polynomialAbsValue f.integralNormalization) p : ℝ)
      exact_mod_cast rootCount_integralNormalization_prime f
        (Nat.pos_of_ne_zero hdeg) p hp (houtside p hpS).1
    rw [hfg, ← hmin]
    exact polynomialRootCoefficients_minpoly_prime K θ p (houtside p hpS).2.1
  obtain ⟨hκ, hmean⟩ := tendsto_summatory_of_idealEulerCorrection_of_degree K
    (polynomialRootCoefficients f) (isMultiplicative_polynomialRootCoefficients f)
    hrnonneg S f.natDegree hrbounded hrgood hmatch
  refine ⟨_, hκ, ?_⟩
  simpa only [arithmeticSummatory_polynomialRootCoefficients] using hmean

/-- The unconditional root-mean theorem in the degree-at-least-two convention,
including all nonmonic polynomials. -/
theorem exists_pos_rootMean_of_irreducible_of_two_le_natDegree
    (f : ℤ[X]) (hf : Irreducible f) (hdeg : 2 ≤ f.natDegree) :
    ∃ κ > (0 : ℝ), Tendsto (fun N : ℕ ↦
      rootCountSummatory (polynomialAbsValue f) N / (N : ℝ)) atTop (𝓝 κ) :=
  exists_pos_rootMean_of_irreducible f hf (by omega)

/-- Every irreducible quadratic has a positive root-count mean and a
natural-cutoff divisor average with twice that mean, with either sign of its
leading coefficient and without any mean hypothesis. -/
theorem quadratic_root_mean_and_divisorAlong
    (f : ℤ[X]) (hf : Irreducible f) (hdeg : f.natDegree = 2) :
    ∃ κ > (0 : ℝ),
      Tendsto (fun N : ℕ ↦ rootCountSummatory (polynomialAbsValue f) N / (N : ℝ))
        atTop (𝓝 κ) ∧
      Tendsto (fun N : ℕ ↦ divisorAlong (polynomialAbsValue f) N /
        ((N : ℝ) * Real.log (N : ℝ))) atTop (𝓝 (2 * κ)) := by
  obtain ⟨κ, hκ, hmean⟩ := exists_pos_rootMean_of_irreducible f hf (by omega)
  exact ⟨κ, hκ, hmean,
    tendsto_polynomial_divisorAlong_of_quadratic_root_mean f hf hdeg hmean⟩

/-- With the original eventual positivity premise, the same positive mean
also gives the original real-cutoff floored divisor average, with constant
`2 * κ`. No monicity or root-count mean premise remains. -/
theorem quadratic_root_mean_and_divisor_average
    (f : ℤ[X]) (hf : Irreducible f) (hdeg : f.natDegree = 2)
    (hpos : ∀ᶠ n : ℤ in atTop, 1 ≤ f.eval n) :
    ∃ κ > (0 : ℝ),
      Tendsto (fun N : ℕ ↦ rootCountSummatory (polynomialAbsValue f) N / (N : ℝ))
        atTop (𝓝 κ) ∧
      Tendsto (fun N : ℕ ↦ divisorAlong (polynomialAbsValue f) N /
        ((N : ℝ) * Real.log (N : ℝ))) atTop (𝓝 (2 * κ)) ∧
      Tendsto (fun x : ℝ ↦ flooredPolynomialSum f x / (x * Real.log x))
        atTop (𝓝 (2 * κ)) := by
  obtain ⟨κ, hκ, hmean, hdivisor⟩ := quadratic_root_mean_and_divisorAlong f hf hdeg
  exact ⟨κ, hκ, hmean, hdivisor,
    tendsto_flooredPolynomialSum_of_quadratic_root_mean f hf hdeg hpos hmean⟩

/-- The unconditional quadratic case of the original inclusive floored sum,
retaining exactly the original eventual positivity hypothesis. -/
theorem quadratic_divisor_average
    (f : ℤ[X]) (hf : Irreducible f) (hdeg : f.natDegree = 2)
    (hpos : ∀ᶠ n : ℤ in atTop, 1 ≤ f.eval n) :
    ∃ c > (0 : ℝ), Tendsto (fun x : ℝ ↦
      (∑ n ∈ Finset.Iic (Nat.floor x),
        (ArithmeticFunction.sigma0 (Nat.floor (f.eval (n : ℤ))) : ℝ)) /
          (x * Real.log x)) atTop (𝓝 c) :=
  quadratic_divisor_average_of_root_mean f hf hdeg hpos
    (exists_pos_rootMean_of_irreducible f hf (by omega))

/-- The original divisor-average conclusion for every nonconstant irreducible
integer polynomial of natural degree at most two. This is deliberately NOT a
theorem for unrestricted degree. -/
theorem erdos_975_of_natDegree_le_two :
    ∀ f : ℤ[X], f.natDegree ≠ 0 → Irreducible f →
      (∀ᶠ n : ℤ in atTop, 1 ≤ f.eval n) → f.natDegree ≤ 2 →
      ∃ c > (0 : ℝ), Tendsto (fun x : ℝ ↦
        (∑ n ∈ Finset.Iic (Nat.floor x),
          (ArithmeticFunction.sigma0 (Nat.floor (f.eval (n : ℤ))) : ℝ)) /
            (x * Real.log x)) atTop (𝓝 c) := by
  intro f hnonconstant hf hpos hdeg
  have hcases : f.natDegree = 1 ∨ f.natDegree = 2 := by omega
  rcases hcases with hlinear | hquadratic
  · exact linear_divisor_average f hlinear hf hpos
  · exact quadratic_divisor_average f hf hquadratic hpos

end Erdos975Support
