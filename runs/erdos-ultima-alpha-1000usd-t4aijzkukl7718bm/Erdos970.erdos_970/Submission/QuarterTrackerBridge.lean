import Submission.QuarterTrackerData
import Submission.QuarterTrackerCorrect

/-! Transfer the checked state computation to the actual phase-weight sums. -/
namespace Erdos970.GapAverages.QuarterExample

lemma weighted_values : weightedChunks 25236 11887 = 33897666 ∧
    weightedChunks 50472 23774 = 13280119881 := by
  have hw := QuarterTracker.run_initial_weights 100947
  rw [QuarterTracker.full_period] at hw
  exact ⟨(weightedChunks_eq 25236 11887).trans hw.1.symm,
    (weightedChunks_eq 50472 23774).trans hw.2.symm⟩

#print axioms weighted_values
end Erdos970.GapAverages.QuarterExample
