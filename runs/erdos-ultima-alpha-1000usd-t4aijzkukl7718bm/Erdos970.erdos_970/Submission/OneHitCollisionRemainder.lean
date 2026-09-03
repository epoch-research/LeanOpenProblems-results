import Submission.OneHitResidueInjection
import Submission.OneHitCoreDyadic

/-! An explicit collision remainder extends the one-hit core correlation bound
to arbitrary tail moduli. Neither the collision remainder nor the core weight
variance is replaced by an unconditional small estimate. -/
namespace Erdos970.OneHitLogConcavity
open Finset GapAverages CoverFibers Resampling

noncomputable def coreCollisionFraction (P R S : Finset ℕ) : ℝ :=
  phaseMean P (fun r => if (∀ p ∈ R,
    Set.InjOn (fun x => x % p) (populationSurvivors S P r)) then 0 else 1)

lemma populationCoveredFraction_le_one (S R : Finset ℕ) (hR : ∀ p ∈ R, p.Prime) :
    populationCoveredFraction S R ≤ 1 := by
  unfold populationCoveredFraction
  have hh := phaseMean_mono R (fun r =>
    show (if (∀ x ∈ S, ∃ p : R, x % p.val = (r p).val) then (1 : ℝ) else 0) ≤ 1 by
      split_ifs <;> norm_num)
  rwa [phaseMean_const R hR] at hh

lemma coreCollisionFraction_nonneg (P R S : Finset ℕ) : 0 ≤ coreCollisionFraction P R S := by
  unfold coreCollisionFraction phaseMean
  exact div_nonneg (sum_nonneg (fun _ _ => by split_ifs <;> norm_num)) (by positivity)

/-- Tail moduli may now repeat within the ambient interval. All exceptional
core phases are retained through an explicit residue-collision term. -/
theorem population_cover_le_core_correlation_add_collisions (P R S T : Finset ℕ)
    (hPR : Disjoint P R) (hR : ∀ p ∈ R, p.Prime) (hST : Disjoint S T) :
    populationCoveredFraction (S ∪ T) (P ∪ R) ≤
      phaseMean P (fun r => coreCoverWeight P R S r*coreCoverWeight P R T r)+
        coreCollisionFraction P R (S ∪ T) := by
  classical
  have hpnt (r : Phase P) : coreCoverWeight P R (S ∪ T) r ≤
      coreCoverWeight P R S r*coreCoverWeight P R T r+
        if (∀ p ∈ R, Set.InjOn (fun x => x % p) (populationSurvivors (S ∪ T) P r))
          then 0 else 1 := by
    split_ifs with hi
    · simpa only [add_zero] using coreCoverWeight_union_le_of_injective P R S T
        (fun p hp => (hR p hp).pos) hST r hi
    · have hh := populationCoveredFraction_le_one (populationSurvivors (S ∪ T) P r) R hR
      have hn := mul_nonneg (coreCoverWeight_nonneg P R S r) (coreCoverWeight_nonneg P R T r)
      change coreCoverWeight P R (S ∪ T) r ≤ 1 at hh
      linarith
  have hh := phaseMean_mono P hpnt
  rw [coreCoverWeight_mean P R _ hPR,phaseMean_add] at hh
  exact hh

/-- Adjacent translates retain both possible sources of loss: the core-weight
second moment and the bad core phases where some residue map is not injective. -/
theorem void_double_le_core_second_moment_add_collisions (P R : Finset ℕ) (m : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hR : ∀ p ∈ R, p.Prime) (hPR : Disjoint P R) :
    coveredFraction (P ∪ R) (2*m) ≤
      phaseMean P (fun r => coreCoverWeight P R (range m) r^2)+
        coreCollisionFraction P R (range (2*m)) := by
  have hh := population_cover_le_core_correlation_add_collisions P R (range m)
    ((range m).image (fun x => m+x)) hPR hR (range_disjoint_translate m m)
  have hsq := phaseMean_mono P (fun r =>
    show coreCoverWeight P R (range m) r*
        coreCoverWeight P R ((range m).image (fun x => m+x)) r ≤
      (coreCoverWeight P R (range m) r^2+
        coreCoverWeight P R ((range m).image (fun x => m+x)) r^2)/2 by
      nlinarith only [sq_nonneg (coreCoverWeight P R (range m) r-
        coreCoverWeight P R ((range m).image (fun x => m+x)) r)])
  rw [phaseMean_div,phaseMean_add,coreCoverWeight_distribution_image_add P R _ hP hR m
    (fun x => x^2),add_self_div_two] at hsq
  rw [← range_split_translate,← void_eq_population,← two_mul m] at hh
  exact hh.trans (by linarith only [hsq])

/-- Fully general finite decomposition, with both nonnegative remainder terms
still present. It is not an unrestricted dyadic void bound. -/
theorem void_double_le_square_add_variance_add_collisions (P R : Finset ℕ) (m : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hR : ∀ p ∈ R, p.Prime) (hPR : Disjoint P R) :
    coveredFraction (P ∪ R) (2*m) ≤ coveredFraction (P ∪ R) m^2+
      coreWeightVariance P R m+coreCollisionFraction P R (range (2*m)) := by
  have hh := void_double_le_core_second_moment_add_collisions P R m hP hR hPR
  rwa [core_weight_second_moment P R m hP hPR] at hh

#print axioms population_cover_le_core_correlation_add_collisions
#print axioms void_double_le_square_add_variance_add_collisions
end Erdos970.OneHitLogConcavity
