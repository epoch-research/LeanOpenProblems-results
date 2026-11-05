/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
import Submission.RootMeanModel
import Submission.RootMeanEulerTransferIdeal
import Submission.QuadraticReduction
import Mathlib.Algebra.Polynomial.SpecificDegree

/-!
# Unconditional root-count means for monic irreducible polynomials

Every nonconstant monic irreducible integer polynomial has a strictly positive
linear root-count mean. The number field is constructed as
`AdjoinRoot (f.map (Int.castRingHom ℚ))`, and its integral generator has minimal
polynomial exactly `f`. Outside a finite set, Kummer–Dedekind identifies the
prime coefficients and finite-modulus Hensel lifting bounds every positive
prime-power coefficient by the degree. At all remaining primes the nonzero
derivative resultant supplies an explicit exponent-independent bound.

The proved ideal Euler-transfer theorem then supplies both convergence and
strict positivity; no root-count mean or Euler summability is assumed.

For monic irreducible quadratics, the existing quadratic reduction also gives
the unconditional divisor average, with constant twice the root-count mean,
including the original floor convention and real cutoffs. Monicity supplies
the eventual positivity needed for that convention.

This does not prove the balanced-divisor estimate in higher degree, or a
root-count mean for nonmonic higher-degree polynomials. No specification or
original conjecture is imported.
-/

namespace Erdos975Support

open Filter Polynomial NumberField Ideal
open scoped Topology

/-- The positive linear root-count mean for every nonconstant monic irreducible
integer polynomial. All number-field, local-bound, correction-summability, and
positivity prerequisites are proved, not hypotheses of this theorem. -/
theorem exists_pos_rootMean_of_monic_irreducible (f : ℤ[X]) (hf : Irreducible f)
    (hmonic : f.Monic) (hdeg : f.natDegree ≠ 0) :
    ∃ κ > (0 : ℝ), Tendsto (fun N : ℕ ↦
      rootCountSummatory (polynomialAbsValue f) N / (N : ℝ)) atTop (𝓝 κ) := by
  classical
  -- The actual number field and integral generator, as in RootMeanModel.
  let F := f.map (Int.castRingHom ℚ)
  have hFirr : Irreducible F :=
    (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
      hmonic.isPrimitive).mp hf
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
    rw [AdjoinRoot.minpoly_root hFirr.ne_zero, hFmonic.leadingCoeff,
      inv_one, C_1, mul_one]
  have hmin : minpoly ℤ θ = f := by
    apply Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
    have he := minpoly.isIntegrallyClosed_eq_field_fractions ℚ K θ.isIntegral
    rw [hminQ] at he
    exact he.symm
  have hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤ := by
    simpa only [pb, AdjoinRoot.powerBasis_gen] using pb.adjoin_gen_eq_top
  -- A finite set containing every conductor-bad or resultant-bad prime.
  let D := RingOfIntegers.exponent θ
  have hD : 0 < D := exponent_pos_of_generator θ hgen
  let R : ℤ := f.resultant f.derivative
  have hR : R ≠ 0 := polynomial_resultant_derivative_ne_zero_of_irreducible f hf hdeg
  have hRabs : 0 < R.natAbs := Int.natAbs_pos.mpr hR
  let S : Finset ℕ := Finset.range (D + R.natAbs + 1)
  have houtside (p : ℕ) (hpS : p ∉ S) :
      ¬ p ∣ D ∧ ¬ (p : ℤ) ∣ R := by
    have hlarge : D + R.natAbs + 1 ≤ p := by
      simpa only [S, Finset.mem_range, not_lt] using hpS
    refine ⟨Nat.not_dvd_of_pos_of_lt hD (by omega), ?_⟩
    rw [Int.natCast_dvd]
    exact Nat.not_dvd_of_pos_of_lt hRabs (by omega)
  -- Supply only proved algebraic data to the unconditional analytic transfer.
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
        p hp (houtside p hpS).2
    change (rootCount (polynomialAbsValue f) (p ^ k) : ℝ) ≤ (f.natDegree : ℝ)
    exact_mod_cast rootCount_polynomial_prime_pow_le f hmonic.isPrimitive p hp hs k hk
  have hmatch (p : ℕ) (hp : p.Prime) (hpS : p ∉ S) :
      polynomialRootCoefficients f p = idealNormCoefficients K p := by
    letI : Fact p.Prime := ⟨hp⟩
    rw [← hmin]
    exact polynomialRootCoefficients_minpoly_prime K θ p (houtside p hpS).1
  obtain ⟨hκ, hmean⟩ := tendsto_summatory_of_idealEulerCorrection_of_degree K
    (polynomialRootCoefficients f) (isMultiplicative_polynomialRootCoefficients f)
    hrnonneg S f.natDegree hrbounded hrgood hmatch
  refine ⟨_, hκ, ?_⟩
  simpa only [arithmeticSummatory_polynomialRootCoefficients] using hmean

/-- The root-mean prerequisite in the degree-at-least-two convention. -/
theorem exists_pos_rootMean_of_monic_irreducible_of_two_le_natDegree
    (f : ℤ[X]) (hf : Irreducible f) (hmonic : f.Monic) (hdeg : 2 ≤ f.natDegree) :
    ∃ κ > (0 : ℝ), Tendsto (fun N : ℕ ↦
      rootCountSummatory (polynomialAbsValue f) N / (N : ℝ)) atTop (𝓝 κ) :=
  exists_pos_rootMean_of_monic_irreducible f hf hmonic (by omega)

/-- A nonconstant monic integer polynomial is eventually positive on integer
inputs. Thus the quadratic floor-sum corollary needs no extra sign hypothesis. -/
theorem polynomial_eval_eventually_pos_of_monic (f : ℤ[X]) (hmonic : f.Monic)
    (hdeg : f.natDegree ≠ 0) :
    ∀ᶠ n : ℤ in atTop, 1 ≤ f.eval n := by
  let P : ℝ[X] := f.map (Int.castRingHom ℝ)
  have hPmonic : P.Monic := hmonic.map _
  have hPdeg : 0 < P.degree := by
    apply natDegree_pos_iff_degree_pos.mp
    dsimp [P]
    rw [Polynomial.natDegree_map_eq_of_injective Int.cast_injective]
    exact Nat.pos_of_ne_zero hdeg
  have ht := (P.tendsto_atTop_of_leadingCoeff_nonneg hPdeg
    (by rw [hPmonic.leadingCoeff]; exact zero_le_one)).comp
    (tendsto_intCast_atTop_atTop : Tendsto (fun n : ℤ ↦ (n : ℝ)) atTop atTop)
  have he := ht.eventually (eventually_ge_atTop (1 : ℝ))
  filter_upwards [he] with n hn
  have hn' : (1 : ℝ) ≤ ((f.eval n : ℤ) : ℝ) := by
    simpa only [Function.comp_def, P, eval_map, eval₂_at_intCast,
      Int.coe_castRingHom, Int.cast_id] using hn
  exact_mod_cast hn'

/-- For a monic irreducible quadratic, both divisor-average conventions have
constant twice its positive root-count mean. No mean or positivity assumption
remains in the hypotheses. -/
theorem monic_quadratic_root_mean_and_divisor_average
    (f : ℤ[X]) (hf : Irreducible f) (hmonic : f.Monic) (hdeg : f.natDegree = 2) :
    ∃ κ > (0 : ℝ),
      Tendsto (fun N : ℕ ↦ rootCountSummatory (polynomialAbsValue f) N / (N : ℝ))
        atTop (𝓝 κ) ∧
      Tendsto (fun N : ℕ ↦ divisorAlong (polynomialAbsValue f) N /
        ((N : ℝ) * Real.log (N : ℝ))) atTop (𝓝 (2 * κ)) ∧
      Tendsto (fun x : ℝ ↦ flooredPolynomialSum f x / (x * Real.log x))
        atTop (𝓝 (2 * κ)) := by
  obtain ⟨κ, hκ, hmean⟩ :=
    exists_pos_rootMean_of_monic_irreducible f hf hmonic (by omega)
  refine ⟨κ, hκ, hmean,
    tendsto_polynomial_divisorAlong_of_quadratic_root_mean f hf hdeg hmean, ?_⟩
  exact tendsto_flooredPolynomialSum_of_quadratic_root_mean f hf hdeg
    (polynomial_eval_eventually_pos_of_monic f hmonic (by omega)) hmean

/-- The unconditional monic quadratic divisor average, using exactly the
original inclusive floor sum and real cutoffs, without importing the spec. -/
theorem monic_quadratic_divisor_average
    (f : ℤ[X]) (hf : Irreducible f) (hmonic : f.Monic) (hdeg : f.natDegree = 2) :
    ∃ c > (0 : ℝ), Tendsto (fun x : ℝ ↦
      (∑ n ∈ Finset.Iic (Nat.floor x),
        (ArithmeticFunction.sigma0 (Nat.floor (f.eval (n : ℤ))) : ℝ)) /
          (x * Real.log x)) atTop (𝓝 c) := by
  obtain ⟨κ, hκ, _, _, hdivisor⟩ :=
    monic_quadratic_root_mean_and_divisor_average f hf hmonic hdeg
  exact ⟨2 * κ, by positivity, hdivisor⟩

private theorem X_sq_add_one_monic : (X ^ 2 + 1 : ℤ[X]).Monic := by
  simpa only [C_1] using monic_X_pow_add_C (1 : ℤ) (by decide : (2 : ℕ) ≠ 0)

private theorem X_sq_add_one_natDegree : (X ^ 2 + 1 : ℤ[X]).natDegree = 2 := by
  simpa only [C_1] using (natDegree_X_pow_add_C (R := ℤ) (n := 2) (r := 1))

private theorem X_sq_add_one_irreducible : Irreducible (X ^ 2 + 1 : ℤ[X]) := by
  apply (X_sq_add_one_monic.irreducible_iff_roots_eq_zero_of_degree_le_three
    (by rw [X_sq_add_one_natDegree]) (by rw [X_sq_add_one_natDegree]; decide)).mpr
  apply Multiset.eq_zero_of_forall_notMem
  intro x hx
  have hx0 := (mem_roots X_sq_add_one_monic.ne_zero).mp hx
  simp only [IsRoot, eval_add, eval_pow, eval_X, eval_one] at hx0
  nlinarith [sq_nonneg x]

/-- Regression: `X² + 1` satisfies the generic monic root-mean prerequisite. -/
theorem exists_pos_rootMean_X_sq_add_one :
    ∃ κ > (0 : ℝ), Tendsto (fun N : ℕ ↦
      rootCountSummatory (polynomialAbsValue (X ^ 2 + 1 : ℤ[X])) N / (N : ℝ))
        atTop (𝓝 κ) :=
  exists_pos_rootMean_of_monic_irreducible (X ^ 2 + 1) X_sq_add_one_irreducible
    X_sq_add_one_monic (by rw [X_sq_add_one_natDegree]; decide)

/-- Regression: the same polynomial also satisfies the unconditional quadratic
floor-sum divisor average. -/
theorem X_sq_add_one_divisor_average :
    ∃ c > (0 : ℝ), Tendsto (fun x : ℝ ↦
      (∑ n ∈ Finset.Iic (Nat.floor x),
        (ArithmeticFunction.sigma0 (Nat.floor ((n : ℤ) ^ 2 + 1)) : ℝ)) /
          (x * Real.log x)) atTop (𝓝 c) := by
  simpa only [eval_add, eval_pow, eval_X, eval_one] using
    monic_quadratic_divisor_average (X ^ 2 + 1) X_sq_add_one_irreducible
      X_sq_add_one_monic X_sq_add_one_natDegree

end Erdos975Support
