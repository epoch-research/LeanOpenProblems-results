import Submission.WeightedCoverageCollision

/-! Transfer of the nonlinear weighted collision cost through a fixed prime
core. The correction is capped by the actual probability of completing the
whole population, rather than by one on every collision phase. No endpoint
estimate for the resulting correction is asserted. -/
namespace Erdos970.OneHitLogConcavity
open Finset GapAverages CoverFibers Resampling
set_option maxHeartbeats 2200000

/-- A probability-weighted remainder for repeated hits across two populations.
The finite recursive cost is retained, and the cap cannot exceed the actual
conditional completion probability. -/
noncomputable def weightedCoreRemainder (P R S T : Finset ℕ) : ℝ :=
  phaseMean P (fun r => min (coreCoverWeight P R (S ∪ T) r)
    (weightedCollisionCost R.toList (populationSurvivors S P r) (populationSurvivors T P r)))

lemma weightedCoreRemainder_nonneg (P R S T : Finset ℕ) :
    0 ≤ weightedCoreRemainder P R S T := by
  unfold weightedCoreRemainder phaseMean
  apply div_nonneg _ (by positivity)
  exact sum_nonneg (fun r _ => le_min (coreCoverWeight_nonneg _ _ _ _) (weightedCollisionCost_nonneg _ _ _))

lemma conditional_cover_le_product_add_capped_cost (P R S T : Finset ℕ)
    (hR : ∀ p ∈ R, 0 < p) (r : Phase P) :
    coreCoverWeight P R (S ∪ T) r ≤ coreCoverWeight P R S r*coreCoverWeight P R T r+
      min (coreCoverWeight P R (S ∪ T) r)
        (weightedCollisionCost R.toList (populationSurvivors S P r) (populationSurvivors T P r)) := by
  have hh := population_cover_le_product_add_weightedCollisionCost R.toList R.nodup_toList
    (fun p hp => hR p (by simpa using hp)) (populationSurvivors S P r) (populationSurvivors T P r)
  have hh' : coreCoverWeight P R (S ∪ T) r ≤ coreCoverWeight P R S r*coreCoverWeight P R T r+
      weightedCollisionCost R.toList (populationSurvivors S P r) (populationSurvivors T P r) := by
    simpa [coreCoverWeight,populationSurvivors_union_population] using hh
  have hprod : 0 ≤ coreCoverWeight P R S r*coreCoverWeight P R T r :=
    mul_nonneg (coreCoverWeight_nonneg _ _ _ _) (coreCoverWeight_nonneg _ _ _ _)
  rw [add_min]
  exact le_min (by linarith only [hprod]) hh'

/-- Full finite-core comparison. The remaining correction is genuinely
weighted by completion probabilities on both sides of each inserted prime. -/
theorem population_cover_le_core_correlation_add_weighted_remainder
    (P R S T : Finset ℕ) (hPR : Disjoint P R) (hR : ∀ p ∈ R, 0 < p) :
    populationCoveredFraction (S ∪ T) (P ∪ R) ≤
      phaseMean P (fun r => coreCoverWeight P R S r*coreCoverWeight P R T r)+
        weightedCoreRemainder P R S T := by
  have hh := phaseMean_mono P (conditional_cover_le_product_add_capped_cost P R S T hR)
  rwa [coreCoverWeight_mean P R _ hPR,phaseMean_add] at hh

lemma weightedCoreRemainder_le_uncapped (P R S T : Finset ℕ) :
    weightedCoreRemainder P R S T ≤ phaseMean P (fun r =>
      weightedCollisionCost R.toList (populationSurvivors S P r) (populationSurvivors T P r)) := by
  exact phaseMean_mono P (fun r => min_le_right _ _)

/-- Unlike a bare collision probability, the remainder cannot exceed the
probability that the full union is actually covered. -/
theorem weightedCoreRemainder_le_coverage (P R S T : Finset ℕ) (hPR : Disjoint P R) :
    weightedCoreRemainder P R S T ≤ populationCoveredFraction (S ∪ T) (P ∪ R) := by
  have hh := phaseMean_mono P (fun r =>
    min_le_left (coreCoverWeight P R (S ∪ T) r)
      (weightedCollisionCost R.toList (populationSurvivors S P r) (populationSurvivors T P r)))
  rwa [coreCoverWeight_mean P R _ hPR] at hh

lemma crossSeparated_core_of_injective (P R S T : Finset ℕ) (hST : Disjoint S T)
    (r : Phase P)
    (hinj : ∀ p ∈ R, Set.InjOn (fun x => x % p) (populationSurvivors (S ∪ T) P r)) :
    CrossSeparated R (populationSurvivors S P r) (populationSurvivors T P r) := by
  intro p hp x hx y hy hxy
  have hxU : x ∈ populationSurvivors (S ∪ T) P r := by
    rw [populationSurvivors_union_population]
    exact mem_union_left _ hx
  have hyU : y ∈ populationSurvivors (S ∪ T) P r := by
    rw [populationSurvivors_union_population]
    exact mem_union_right _ hy
  have heq := hinj p hp hxU hyU hxy
  subst y
  exact disjoint_left.mp hST (mem_filter.mp hx).1 (mem_filter.mp hy).1

/-- The new correction is no worse than the old all-or-nothing collision
remainder for disjoint populations; on injective phases the recursive cost
vanishes exactly. -/
theorem weightedCoreRemainder_le_collision (P R S T : Finset ℕ)
    (hR : ∀ p ∈ R, p.Prime) (hST : Disjoint S T) :
    weightedCoreRemainder P R S T ≤ coreCollisionFraction P R (S ∪ T) := by
  classical
  unfold weightedCoreRemainder coreCollisionFraction
  apply phaseMean_mono
  intro r
  split_ifs with hi
  · have hsep := crossSeparated_core_of_injective P R S T hST r hi
    have hz := weightedCollisionCost_zero_of_crossSeparated R.toList
      (populationSurvivors S P r) (populationSurvivors T P r) (by simpa using hsep)
    rw [hz]
    exact min_le_right _ _
  · exact (min_le_left _ _).trans (populationCoveredFraction_le_one _ R hR)

/-- Adjacent blocks keep the full core-weight variance and the new weighted
remainder. Neither is asserted to have the small relative size needed for
the square-cubic endpoint reduction. -/
theorem void_double_le_square_add_variance_add_weighted_remainder
    (P R : Finset ℕ) (m : ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hR : ∀ p ∈ R, p.Prime) (hPR : Disjoint P R) :
    coveredFraction (P ∪ R) (2*m) ≤ coveredFraction (P ∪ R) m^2+
      coreWeightVariance P R m+
        weightedCoreRemainder P R (range m) ((range m).image (fun x => m+x)) := by
  have hh := population_cover_le_core_correlation_add_weighted_remainder P R
    (range m) ((range m).image (fun x => m+x)) hPR (fun p hp => (hR p hp).pos)
  have hsq := phaseMean_mono P (fun r =>
    show coreCoverWeight P R (range m) r*coreCoverWeight P R ((range m).image (fun x => m+x)) r ≤
      (coreCoverWeight P R (range m) r^2+
        coreCoverWeight P R ((range m).image (fun x => m+x)) r^2)/2 by
          nlinarith only [sq_nonneg (coreCoverWeight P R (range m) r-
            coreCoverWeight P R ((range m).image (fun x => m+x)) r)])
  rw [phaseMean_div,phaseMean_add,coreCoverWeight_distribution_image_add P R _ hP hR m
    (fun x => x^2),add_self_div_two] at hsq
  rw [← range_split_translate,← void_eq_population,← two_mul m] at hh
  have hfin := hh.trans (add_le_add hsq le_rfl)
  rwa [core_weight_second_moment P R m hP hPR] at hfin

#print axioms population_cover_le_core_correlation_add_weighted_remainder
#print axioms weightedCoreRemainder_le_coverage
#print axioms weightedCoreRemainder_le_collision
#print axioms void_double_le_square_add_variance_add_weighted_remainder
end Erdos970.OneHitLogConcavity
