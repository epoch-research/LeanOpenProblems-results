import Submission.DyadicLowPrimeBoundary

/-! Both moving boundary contributions have convergent unnormalized harmonic
partial sums. The intervening signed comparison sum remains unestimated. -/
namespace Erdos371
open Finset Filter FiniteInformation
open scoped Topology
set_option autoImplicit false

noncomputable def dyadicLowNotHighSign (n : ℕ) : ℝ := by
  classical
  exact if dyadicLowLoser n ∧ ¬dyadicPrimeThreshold threeQuarterBandWidth n < (primeWinner n : ℝ)
    then factorSign n else 0

noncomputable def dyadicInteriorSign (n : ℕ) : ℝ := by
  classical
  exact if dyadicLowLoser n ∨ dyadicPrimeThreshold threeQuarterBandWidth n < (primeWinner n : ℝ)
    then 0 else factorSign n

lemma factorSign_dyadic_boundaries (n : ℕ) :
    factorSign n-dyadicInteriorSign n =
      dyadicHighWinnerSign threeQuarterBandWidth n+dyadicLowNotHighSign n := by
  classical
  unfold dyadicInteriorSign dyadicHighWinnerSign dyadicLowNotHighSign
  by_cases hl : dyadicLowLoser n <;>
    by_cases hh : dyadicPrimeThreshold threeQuarterBandWidth n < (primeWinner n : ℝ) <;> simp [hl,hh]

lemma dyadicInteriorSign_eq (n : ℕ) : dyadicInteriorSign n =
    if lowPrimeBandCutoff (Nat.log 2 n) ≤ primeLoser n ∧
        (primeWinner n : ℝ) ≤ dyadicPrimeThreshold threeQuarterBandWidth n
    then factorSign n else 0 := by
  classical
  unfold dyadicInteriorSign dyadicLowLoser
  have he : (¬(primeLoser n < lowPrimeBandCutoff (Nat.log 2 n) ∨
      dyadicPrimeThreshold threeQuarterBandWidth n < (primeWinner n : ℝ))) ↔
      (lowPrimeBandCutoff (Nat.log 2 n) ≤ primeLoser n ∧
        (primeWinner n : ℝ) ≤ dyadicPrimeThreshold threeQuarterBandWidth n) := by simp
  simp only [← he,ite_not]
  split_ifs <;> rfl

lemma dyadicLowNotHighSign_harmonic_norm_le (n : ℕ) :
    ‖dyadicLowNotHighSign n/(n : ℝ)‖ ≤ dyadicLowLoserReciprocal n := by
  classical
  unfold dyadicLowNotHighSign dyadicLowLoserReciprocal
  by_cases hl : dyadicLowLoser n
  · simp only [hl,true_and,if_true]
    split_ifs
    · simp only [zero_div,norm_zero]
      positivity
    · rw [norm_div,factorSign_norm,Real.norm_natCast]
  · simp [hl]

theorem summable_dyadicLowNotHighSign_harmonic :
    Summable (fun n => dyadicLowNotHighSign n/(n : ℝ)) :=
  summable_dyadicLowLoserReciprocal.of_norm_bounded dyadicLowNotHighSign_harmonic_norm_le

/-- The actual discarded contribution, not just its normalized harmonic
mean, has a convergent ordinarily ordered harmonic series. The overlap of
the two boundary events is accounted for by lowNotHighSign. -/
theorem dyadic_boundary_rawHarmonic_converges :
    ∃ L : ℝ, Tendsto (rawHarmonicSum (fun n => factorSign n-dyadicInteriorSign n)) atTop (𝓝 L) := by
  obtain ⟨H,hH⟩ := threeQuarterHighWinner_rawHarmonic_converges
  have hL := summable_dyadicLowNotHighSign_harmonic.hasSum.tendsto_sum_nat
  refine ⟨H+∑' n, dyadicLowNotHighSign n/(n : ℝ),?_⟩
  convert hH.add hL using 1
  funext N
  simp only [rawHarmonicSum,factorSign_dyadic_boundaries,add_div,sum_add_distrib]

/-- Removing these two moving boundaries changes the ordinary signed mean
by a quantity tending to zero. No mean limit for interiorSign is asserted. -/
theorem dyadic_boundary_natural_mean_zero :
    Tendsto (fun N => prefixMean N (fun n => factorSign n-dyadicInteriorSign n)) atTop (𝓝 0) := by
  obtain ⟨L,hL⟩ := dyadic_boundary_rawHarmonic_converges
  exact prefixMean_zero_of_rawHarmonicSum_tendsto _ L hL

#print axioms summable_dyadicLowNotHighSign_harmonic
#print axioms dyadic_boundary_rawHarmonic_converges
#print axioms dyadic_boundary_natural_mean_zero
end Erdos371
