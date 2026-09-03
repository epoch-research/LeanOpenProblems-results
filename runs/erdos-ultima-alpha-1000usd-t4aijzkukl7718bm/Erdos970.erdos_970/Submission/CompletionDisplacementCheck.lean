import Submission.CompletionDisplacementBounds
namespace Erdos970.OneHitLogConcavity
open Finset GapAverages CoverFibers Resampling
set_option maxHeartbeats 2000000

example : populationCoveredFraction ({0} : Finset ℕ) ({3} : Finset ℕ) = (1/3 : ℝ) := by
  rw [show ({3} : Finset ℕ) = insert 3 ∅ from rfl,
    populationCoveredFraction_insert_avoid _ _ _ (by simp)]
  simp only [residueMean, Fin.sum_univ_succ]
  norm_num [avoidClass, populationCoveredFraction_empty_moduli]

example : coverageCovariance ({2,3} : Finset ℕ) {0} {0} = (2/9 : ℝ) := by
  unfold coverageCovariance
  norm_num only [union_self]
  have h : populationCoveredFraction ({0} : Finset ℕ) ({2,3} : Finset ℕ) = (2/3 : ℝ) := by
    rw [populationCoveredFraction_insert_avoid _ _ _ (by simp)]
    simp only [residueMean, Fin.sum_univ_succ]
    norm_num [avoidClass]
    rw [show ({3} : Finset ℕ) = insert 3 ∅ from rfl]
    simp_rw [populationCoveredFraction_insert_avoid (∅ : Finset ℕ) _ 3 (by simp)]
    simp only [residueMean, Fin.sum_univ_succ]
    norm_num [avoidClass, populationCoveredFraction_empty_moduli]
  rw [h]
  norm_num
end Erdos970.OneHitLogConcavity
