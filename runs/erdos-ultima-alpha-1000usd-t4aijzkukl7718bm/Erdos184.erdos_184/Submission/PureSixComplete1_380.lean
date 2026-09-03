import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_380_0 : CompleteAt 380 0 := by decide +kernel
lemma complete_380_1 : CompleteAt 380 1 := by decide +kernel
lemma complete_380_2 : CompleteAt 380 2 := by decide +kernel
lemma complete_380_3 : CompleteAt 380 3 := by decide +kernel
lemma complete_380_4 : CompleteAt 380 4 := by decide +kernel
lemma complete_case380 : ∀ e0, CompleteAt 380 e0 := by
  intro e0
  fin_cases e0
  · exact complete_380_0
  · exact complete_380_1
  · exact complete_380_2
  · exact complete_380_3
  · exact complete_380_4
#print axioms complete_case380
end Erdos184Work.PureSixLocalFilter1
