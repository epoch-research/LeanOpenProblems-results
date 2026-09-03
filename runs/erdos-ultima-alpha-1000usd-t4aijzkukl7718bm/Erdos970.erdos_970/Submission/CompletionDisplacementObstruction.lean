import Submission.CompletionDisplacementBounds

/-! Exact obstruction to discarding the recursive child covariance after
averaging over the newly inserted prime. These statements are not a
counterexample to the Jacobsthal conjecture. -/
namespace Erdos970.OneHitLogConcavity
open Finset GapAverages CoverFibers Resampling
set_option maxHeartbeats 2000000

/-- A complete period for the inserted prime does not make the full
covariance sum vanish. -/
theorem two_prime_covariance_short_sum :
    (∑ d ∈ range 2, coverageCovariance ({2,3} : Finset ℕ)
      {0} (({0} : Finset ℕ).image (fun x => d+x))) = (1/9 : ℝ) := by
  simp only [sum_range_succ, sum_range_zero, zero_add, image_singleton,
    coverageCovariance]
  simp_rw [populationCoveredFraction_insert_avoid ({3} : Finset ℕ) _ 2 (by simp)]
  simp only [show ({3} : Finset ℕ) = insert 3 ∅ from rfl]
  simp_rw [populationCoveredFraction_insert_avoid (∅ : Finset ℕ) _ 3 (by simp)]
  simp only [residueMean, Fin.sum_univ_succ]
  norm_num [avoidClass, populationCoveredFraction_empty_moduli]

/-- Averaging over the product period does cancel the full covariance in
this example; the smaller averaging period was the obstruction. -/
theorem two_prime_covariance_full_sum :
    (∑ d ∈ range 6, coverageCovariance ({2,3} : Finset ℕ)
      {0} (({0} : Finset ℕ).image (fun x => d+x))) = 0 := by
  simp only [sum_range_succ, sum_range_zero, zero_add, image_singleton,
    coverageCovariance]
  simp_rw [populationCoveredFraction_insert_avoid ({3} : Finset ℕ) _ 2 (by simp)]
  simp only [show ({3} : Finset ℕ) = insert 3 ∅ from rfl]
  simp_rw [populationCoveredFraction_insert_avoid (∅ : Finset ℕ) _ 3 (by simp)]
  simp only [residueMean, Fin.sum_univ_succ]
  norm_num [avoidClass, populationCoveredFraction_empty_moduli]

/-- In the same example the one-prime sources do cancel exactly. -/
theorem two_prime_source_short_sum :
    (∑ d ∈ range 2, signedCompletionSource ({3} : Finset ℕ)
      {0} (({0} : Finset ℕ).image (fun x => d+x)) 2) = 0 := by
  have h := signedCompletionSource_displacement_mean_zero ({3} : Finset ℕ)
    {0} {0} (by simpa using Nat.prime_three) 2 (by norm_num)
  simp only [residueMean, Fin.sum_univ_succ] at h
  norm_num only [Fin.val_zero, Fin.val_succ, Nat.cast_ofNat, add_zero, zero_add,
    Nat.reduceAdd] at h
  simp only [sum_range_succ, sum_range_zero, zero_add]
  linarith only [h]

/-- The nonzero short-period covariance is entirely in the recursive child.
In particular that term is positive, even after a complete period for 2. -/
theorem two_prime_child_short_sum :
    (∑ d ∈ range 2, residueMean 2 (fun a => coverageCovariance ({3} : Finset ℕ)
      (avoidClass {0} 2 a)
      (avoidClass (({0} : Finset ℕ).image (fun x => d+x)) 2 a))) = (1/9 : ℝ) := by
  have he (d : ℕ) := coverageCovariance_insert_signed ({3} : Finset ℕ) {0}
    (({0} : Finset ℕ).image (fun x => d+x)) 2 (by simp) (by norm_num)
  have hs := sum_congr (s₁ := range 2) rfl (fun d _ => he d)
  rw [sum_add_distrib, two_prime_source_short_sum, add_zero] at hs
  exact hs.symm.trans two_prime_covariance_short_sum

#print axioms two_prime_covariance_short_sum
#print axioms two_prime_covariance_full_sum
#print axioms two_prime_source_short_sum
#print axioms two_prime_child_short_sum
end Erdos970.OneHitLogConcavity
