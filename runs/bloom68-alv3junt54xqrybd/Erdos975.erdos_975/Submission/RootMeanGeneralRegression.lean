/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
import Submission.RootMeanGeneral
import Mathlib.Tactic.ComputeDegree

/-!
# Nonmonic regression callers for the general root-mean theorem

These callers check the actual root counts and inclusive floor sums, not an
abstract coefficient sequence. Where indicated, irreducibility is supplied by
the caller; no monicity, root-mean, or Euler summability premise is supplied.
The degree-three and negative-leading-coefficient checks concern root means
only, not the original floored divisor average. The fixed-divisor check has
`ρ(2) = 2`, `ρ(4) = 0`, so it also exercises the bad-local-factor situation
where inverting the polynomial root series would be inappropriate.
-/

namespace Erdos975Support

open Filter Polynomial
open scoped Topology

private theorem two_X_pow_add_one_natDegree (d : ℕ) :
    (C (2 : ℤ) * X ^ d + 1 : ℤ[X]).natDegree = d := by
  simpa only [← C_1, natDegree_add_C] using
    natDegree_C_mul_X_pow d (2 : ℤ) (by decide)

private theorem two_X_sq_add_one_leadingCoeff :
    (C (2 : ℤ) * X ^ 2 + 1 : ℤ[X]).leadingCoeff = 2 := by
  rw [leadingCoeff, two_X_pow_add_one_natDegree]
  norm_num [coeff_one]

/-- The primary quadratic regression is genuinely nonmonic. -/
theorem two_X_sq_add_one_not_monic : ¬ (C (2 : ℤ) * X ^ 2 + 1 : ℤ[X]).Monic := by
  intro hm
  have h := hm.leadingCoeff
  rw [two_X_sq_add_one_leadingCoeff] at h
  norm_num at h

/-- `2 X² + 1` has the unconditional positive mean, given irreducibility. -/
theorem exists_pos_rootMean_two_X_sq_add_one
    (hf : Irreducible (C (2 : ℤ) * X ^ 2 + 1 : ℤ[X])) :
    ∃ κ > (0 : ℝ), Tendsto (fun N : ℕ ↦
      rootCountSummatory (polynomialAbsValue (C (2 : ℤ) * X ^ 2 + 1 : ℤ[X])) N /
        (N : ℝ)) atTop (𝓝 κ) :=
  exists_pos_rootMean_of_irreducible _ hf (by rw [two_X_pow_add_one_natDegree]; decide)

private theorem two_X_sq_add_one_eventually_pos :
    ∀ᶠ n : ℤ in atTop, 1 ≤ (C (2 : ℤ) * X ^ 2 + 1 : ℤ[X]).eval n := by
  apply Filter.Eventually.of_forall
  intro n
  simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X, eval_one]
  nlinarith [sq_nonneg n]

/-- The quadratic corollary uses the literal original sum for `2 n² + 1`. -/
theorem two_X_sq_add_one_divisor_average
    (hf : Irreducible (C (2 : ℤ) * X ^ 2 + 1 : ℤ[X])) :
    ∃ c > (0 : ℝ), Tendsto (fun x : ℝ ↦
      (∑ n ∈ Finset.Iic (Nat.floor x),
        (ArithmeticFunction.sigma0 (Nat.floor (2 * (n : ℤ) ^ 2 + 1)) : ℝ)) /
          (x * Real.log x)) atTop (𝓝 c) := by
  simpa only [eval_add, eval_mul, eval_C, eval_pow, eval_X, eval_one] using
    quadratic_divisor_average _ hf (two_X_pow_add_one_natDegree 2)
      two_X_sq_add_one_eventually_pos

/-- The restricted original theorem also accepts the nonmonic quadratic. -/
theorem two_X_sq_add_one_degree_le_two_average
    (hf : Irreducible (C (2 : ℤ) * X ^ 2 + 1 : ℤ[X])) :
    ∃ c > (0 : ℝ), Tendsto (fun x : ℝ ↦
      flooredPolynomialSum (C (2 : ℤ) * X ^ 2 + 1 : ℤ[X]) x /
        (x * Real.log x)) atTop (𝓝 c) :=
  erdos_975_of_natDegree_le_two _ (by rw [two_X_pow_add_one_natDegree]; decide)
    hf two_X_sq_add_one_eventually_pos (by rw [two_X_pow_add_one_natDegree])

/-- The restricted theorem covers the nonmonic linear branch as well. -/
theorem two_X_add_one_degree_le_two_average
    (hf : Irreducible (C (2 : ℤ) * X + 1 : ℤ[X])) :
    ∃ c > (0 : ℝ), Tendsto (fun x : ℝ ↦
      (∑ n ∈ Finset.Iic (Nat.floor x),
        (ArithmeticFunction.sigma0 (Nat.floor (2 * (n : ℤ) + 1)) : ℝ)) /
          (x * Real.log x)) atTop (𝓝 c) := by
  have hd : (C (2 : ℤ) * X + 1 : ℤ[X]).natDegree = 1 := by
    simpa only [pow_one] using two_X_pow_add_one_natDegree 1
  have hpos : ∀ᶠ n : ℤ in atTop, 1 ≤ (C (2 : ℤ) * X + 1 : ℤ[X]).eval n := by
    filter_upwards [eventually_ge_atTop (0 : ℤ)] with n hn
    simp only [eval_add, eval_mul, eval_C, eval_X, eval_one]
    omega
  simpa only [eval_add, eval_mul, eval_C, eval_X, eval_one] using
    erdos_975_of_natDegree_le_two _ (by omega) hf hpos (by omega)

/-- The nonmonic cubic check proves a root mean, NOT a divisor average. -/
theorem exists_pos_rootMean_two_X_cube_add_one
    (hf : Irreducible (C (2 : ℤ) * X ^ 3 + 1 : ℤ[X])) :
    ∃ κ > (0 : ℝ), Tendsto (fun N : ℕ ↦
      rootCountSummatory (polynomialAbsValue (C (2 : ℤ) * X ^ 3 + 1 : ℤ[X])) N /
        (N : ℝ)) atTop (𝓝 κ) :=
  exists_pos_rootMean_of_irreducible _ hf (by rw [two_X_pow_add_one_natDegree]; decide)

/-- Negative leading coefficients need no sign premise in the root mean. -/
theorem exists_pos_rootMean_neg_two_X_sq_add_one
    (hf : Irreducible (-(C (2 : ℤ) * X ^ 2 + 1) : ℤ[X])) :
    ∃ κ > (0 : ℝ), Tendsto (fun N : ℕ ↦
      rootCountSummatory (polynomialAbsValue (-(C (2 : ℤ) * X ^ 2 + 1) : ℤ[X])) N /
        (N : ℝ)) atTop (𝓝 κ) :=
  exists_pos_rootMean_of_irreducible _ hf
    (by rw [natDegree_neg, two_X_pow_add_one_natDegree]; decide)

/-- Good COMPOSITE moduli are also preserved by normalization. -/
theorem two_X_sq_add_one_normalization_mod_nine :
    rootCount (polynomialAbsValue (C (2 : ℤ) * X ^ 2 + 1 : ℤ[X])) 9 =
      rootCount (polynomialAbsValue
        (C (2 : ℤ) * X ^ 2 + 1 : ℤ[X]).integralNormalization) 9 := by
  apply rootCount_integralNormalization_of_coprime
    _ (by rw [two_X_pow_add_one_natDegree]; decide) 9
  rw [two_X_sq_add_one_leadingCoeff]
  decide

/-- An explicit nonmonic fixed-divisor example has local
root coefficients `ρ(2) = 2`, `ρ(4) = 0`; no irreducibility is needed to count. -/
theorem fixed_divisor_bad_local_regression :
    rootCount (polynomialAbsValue
      (C (3 : ℤ) * X ^ 4 + C 3 * X ^ 2 + C 2 * X + C 2 : ℤ[X])) 2 = 2 ∧
    rootCount (polynomialAbsValue
      (C (3 : ℤ) * X ^ 4 + C 3 * X ^ 2 + C 2 * X + C 2 : ℤ[X])) 4 = 0 := by
  norm_num [rootCount, polynomialAbsValue, Finset.range_add_one,
    Finset.filter_insert, Finset.filter_singleton]

/-- The actual ideal correction still applies to that bad-local-factor
example; as elsewhere in these regression callers, irreducibility is a premise. -/
theorem exists_pos_rootMean_nonmonic_fixed_divisor
    (hf : Irreducible
      (C (3 : ℤ) * X ^ 4 + C 3 * X ^ 2 + C 2 * X + C 2 : ℤ[X])) :
    ∃ κ > (0 : ℝ), Tendsto (fun N : ℕ ↦ rootCountSummatory (polynomialAbsValue
      (C (3 : ℤ) * X ^ 4 + C 3 * X ^ 2 + C 2 * X + C 2 : ℤ[X])) N /
        (N : ℝ)) atTop (𝓝 κ) := by
  have hd :
      (C (3 : ℤ) * X ^ 4 + C 3 * X ^ 2 + C 2 * X + C 2 : ℤ[X]).natDegree = 4 := by
    compute_degree!
  exact exists_pos_rootMean_of_irreducible _ hf (by omega)

end Erdos975Support
