import Submission.RootMeanConvolution
import Submission.RootMeanKummer

/-!
# Number-field coefficient means for the root-mean route

The norm-counting coefficients of a number field have an unconditional,
strictly positive linear mean. This file supplies the exact coefficient
summatory/cardinality identity, derives the mean from Mathlib's nonzero ideal
counting theorem, and applies the proved Dirichlet-convolution transfer lemma.

At good primes the coefficients agree with polynomial root counts for an
integral minimal polynomial, by the bijection proved in `RootMeanKummer`.
No identification at prime powers, summable polynomial Euler correction, or
general polynomial root-count mean is assumed or claimed.
-/

namespace Erdos975Support

open Filter Polynomial NumberField Ideal
open scoped Topology nonZeroDivisors

/-- Polynomial root counts as a real arithmetic function, using the existing
zero-modulus convention. -/
noncomputable def polynomialRootCoefficients (f : ℤ[X]) : ArithmeticFunction ℝ :=
  ⟨fun q ↦ (rootCount (polynomialAbsValue f) q : ℝ), by simp⟩

/-- Its summatory function is exactly the one already used by the project. -/
theorem arithmeticSummatory_polynomialRootCoefficients (f : ℤ[X]) (N : ℕ) :
    arithmeticSummatory (polynomialRootCoefficients f) N =
      rootCountSummatory (polynomialAbsValue f) N := rfl

/-- Ideal norm coefficients, with the zero ideal omitted at coefficient zero.
At every positive index this is precisely the Dedekind zeta coefficient. -/
noncomputable def idealNormCoefficients (K : Type*) [Field K] [NumberField K] :
    ArithmeticFunction ℝ :=
  ⟨fun n ↦ if n = 0 then 0 else (Nat.card {I : Ideal (𝓞 K) // absNorm I = n} : ℝ),
    by simp⟩

/-- The integer fiber-counting identity, including the zero-cutoff case. -/
theorem sum_card_absNorm_eq_card_nonzero_norm_le (K : Type*) [Field K] [NumberField K]
    (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, Nat.card {I : Ideal (𝓞 K) // absNorm I = n}) =
      Nat.card {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) ≤ N} := by
  classical
  rw [← add_left_inj 1, ← card_norm_le_eq_card_norm_le_add_one,
    show 1 = Nat.card {I : Ideal (𝓞 K) // absNorm I = 0} by simp [Ideal.absNorm_eq_zero_iff],
    Finset.sum_Ioc_add_eq_sum_Icc N.zero_le,
    ← Finset.card_preimage_eq_sum_card_image_eq (fun n _ ↦ finite_setOf_absNorm_eq n)]
  simp [Set.coe_eq_subtype]

/-- Exact positive-index ideal summation as a nonzero ideal count. -/
theorem arithmeticSummatory_idealNormCoefficients (K : Type*) [Field K] [NumberField K]
    (N : ℕ) :
    arithmeticSummatory (idealNormCoefficients K) N =
      (Nat.card {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) ≤ N} : ℝ) := by
  classical
  unfold arithmeticSummatory
  have hterm (n : ℕ) (hn : n ∈ Finset.Ioc 0 N) :
      idealNormCoefficients K n = (Nat.card {I : Ideal (𝓞 K) // absNorm I = n} : ℝ) := by
    simp only [idealNormCoefficients, ArithmeticFunction.coe_mk,
      if_neg (Finset.mem_Ioc.mp hn).1.ne']
  rw [Finset.sum_congr rfl hterm, ← Nat.cast_sum, sum_card_absNorm_eq_card_nonzero_norm_le]

/-- The unconditional linear mean of the ideal coefficients. Its limit is
Mathlib's positive Dedekind zeta residue. -/
theorem tendsto_idealNormCoefficients_mean (K : Type*) [Field K] [NumberField K] :
    Tendsto (fun N : ℕ ↦ arithmeticSummatory (idealNormCoefficients K) N / (N : ℝ))
      atTop (𝓝 (dedekindZeta_residue K)) := by
  have ht := (NumberField.Ideal.tendsto_norm_le_div_atTop₀ K).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ ↦ (N : ℝ)) atTop atTop)
  simpa only [Function.comp_def, Nat.cast_le, arithmeticSummatory_idealNormCoefficients,
    dedekindZeta_residue] using ht

/-- An existence formulation of the ideal mean, with positivity proved rather
than assumed. -/
theorem exists_pos_idealNormCoefficients_mean (K : Type*) [Field K] [NumberField K] :
    ∃ κ > (0 : ℝ), Tendsto (fun N : ℕ ↦
      arithmeticSummatory (idealNormCoefficients K) N / (N : ℝ)) atTop (𝓝 κ) :=
  ⟨dedekindZeta_residue K, dedekindZeta_residue_pos K,
    tendsto_idealNormCoefficients_mean K⟩

/-- The first-order Euler coefficients agree at every conductor-good prime. -/
theorem polynomialRootCoefficients_minpoly_prime (K : Type*) [Field K] [NumberField K]
    (θ : 𝓞 K) (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ RingOfIntegers.exponent θ) :
    polynomialRootCoefficients (minpoly ℤ θ) p = idealNormCoefficients K p := by
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  simp only [polynomialRootCoefficients, idealNormCoefficients, ArithmeticFunction.coe_mk,
    if_neg hp0]
  exact_mod_cast rootCount_minpoly_eq_card_absNorm_prime θ p hp

/-- The number-field convolution limit, now requiring only the explicitly
stated summability of the correction coefficients. The ideal-counting limit
itself is supplied by the proved theorem above. -/
theorem tendsto_idealNormCoefficients_convolution (K : Type*) [Field K] [NumberField K]
    (b : ArithmeticFunction ℝ) (hb : Summable (fun d : ℕ ↦ ‖b d / (d : ℝ)‖)) :
    Tendsto (fun N : ℕ ↦
      arithmeticSummatory (idealNormCoefficients K * b) N / (N : ℝ)) atTop
      (𝓝 (dedekindZeta_residue K * ∑' d : ℕ, b d / (d : ℝ))) :=
  tendsto_summatory_dirichletConvolution (idealNormCoefficients K) b
    (tendsto_idealNormCoefficients_mean K) hb

end Erdos975Support
