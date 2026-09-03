import Submission.CompletionFullPeriod

/-! An exact obstruction to replacing the full-period factor by an additive
prime budget for arbitrary separated translations. The offset here is 35,
not the adjacent-block offset in the target correlation problem. -/
namespace Erdos970.OneHitLogConcavity
open Finset GapAverages CoverFibers Resampling
set_option maxHeartbeats 5000000
set_option maxRecDepth 2000

lemma two_point_five_seven_cover :
    populationCoveredFraction ({0,1} : Finset ℕ) {5,7} = (2/35 : ℝ) := by
  rw [populationCoveredFraction_insert_avoid _ _ _ (by simp)]
  simp only [show ({7} : Finset ℕ) = insert 7 ∅ from rfl]
  simp_rw [populationCoveredFraction_insert_avoid (∅ : Finset ℕ) _ 7 (by simp)]
  simp only [residueMean,Fin.sum_univ_succ]
  norm_num [avoidClass,populationCoveredFraction_empty_moduli]

lemma separated_two_point_covariance_sum :
    (∑ d ∈ range 2, coverageCovariance ({5,7} : Finset ℕ) {0,1}
      (({35,36} : Finset ℕ).image (fun x => d+x))) = (62/1225 : ℝ) := by
  simp only [sum_range_succ,sum_range_zero,zero_add,image_insert,image_singleton,
    coverageCovariance]
  simp_rw [populationCoveredFraction_insert_avoid ({7} : Finset ℕ) _ 5 (by simp)]
  simp only [show ({7} : Finset ℕ) = insert 7 ∅ from rfl]
  simp_rw [populationCoveredFraction_insert_avoid (∅ : Finset ℕ) _ 7 (by simp)]
  simp only [residueMean,Fin.sum_univ_succ]
  norm_num [avoidClass,populationCoveredFraction_empty_moduli]

/-- Disjointness and a displacement range as long as each population do not,
by themselves, justify an additive prime-cost replacement. -/
theorem separated_relative_additive_bound_fails :
    (∑ p ∈ ({5,7} : Finset ℕ), (p : ℝ))*
        (populationCoveredFraction ({0,1} : Finset ℕ) {5,7})^2 <
      |∑ d ∈ range 2, coverageCovariance ({5,7} : Finset ℕ) {0,1}
        (({35,36} : Finset ℕ).image (fun x => d+x))| := by
  rw [two_point_five_seven_cover,separated_two_point_covariance_sum]
  norm_num

theorem separated_example_disjoint (d : ℕ) :
    Disjoint ({0,1} : Finset ℕ) (({35,36} : Finset ℕ).image (fun x => d+x)) := by
  simp only [disjoint_left,mem_insert,mem_singleton,mem_image]
  rintro x (rfl | rfl) ⟨y,hy,he⟩ <;> rcases hy with rfl | rfl <;> omega

#print axioms separated_relative_additive_bound_fails
#print axioms separated_example_disjoint
end Erdos970.OneHitLogConcavity
