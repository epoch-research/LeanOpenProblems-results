import Submission.SquareRootReciprocal
import Submission.Density

/-!
# The remaining higher-root series problem

The root parameters 1 and 2 can now be removed from the exact series
characterization of Erdős 821. The remaining assertion for all k>=3 is not
proved or disproved here.
-/

open Nat Filter
open scoped Classical

namespace Erdos821

lemma small_root_predecessor_series_divergence (k : ℕ) (hk : k ≤ 2)
    (s : ℝ) (hs : s ≤ 1) :
    ¬Summable ((smoothShiftedPredecessors k).indicator (fun d : ℕ => (d : ℝ) ^ (-s))) := by
  intro H
  apply square_root_predecessor_series_divergence s hs
  refine H.of_nonneg_of_le (fun d => Set.indicator_nonneg
    (fun d _ => Real.rpow_nonneg (Nat.cast_nonneg d) _) d) ?_
  intro d
  by_cases hd : d ∈ smoothShiftedPredecessors 2
  · have hdk := smoothShiftedPredecessors_antitone hk hd
    rw [Set.indicator_of_mem hd, Set.indicator_of_mem hdk]
  · rw [Set.indicator_of_notMem hd]
    exact Set.indicator_nonneg (fun d _ => Real.rpow_nonneg (Nat.cast_nonneg d) _) d

/-- Exact equivalent formulation after removing the root cases already established. -/
theorem erdos_821_iff_higher_root_series :
    (∀ ε > (0 : ℝ), {n : ℕ | (g n : ℝ) > (n : ℝ) ^ (1 - ε)}.Infinite) ↔
      ∀ k : ℕ, 3 ≤ k → ∀ s : ℝ, s < 1 →
        ¬Summable ((smoothShiftedPredecessors k).indicator (fun d : ℕ => (d : ℝ) ^ (-s))) := by
  rw [erdos_821_iff_smooth_shifted_all_exponents]
  constructor
  · intro H k hk s hs
    exact H k (by omega) s hs
  · intro H k hk s hs
    by_cases hk3 : 3 ≤ k
    · exact H k hk3 s hs
    · exact small_root_predecessor_series_divergence k (by omega) s hs.le

end Erdos821
