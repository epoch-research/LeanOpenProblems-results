import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_385_0 : CompleteAt 385 0 := by decide +kernel
lemma complete_385_1 : CompleteAt 385 1 := by decide +kernel
lemma complete_385_2 : CompleteAt 385 2 := by decide +kernel
lemma complete_385_3 : CompleteAt 385 3 := by decide +kernel
lemma complete_385_4 : CompleteAt 385 4 := by decide +kernel
lemma complete_case385 : ∀ e0, CompleteAt 385 e0 := by
  intro e0
  fin_cases e0
  · exact complete_385_0
  · exact complete_385_1
  · exact complete_385_2
  · exact complete_385_3
  · exact complete_385_4
#print axioms complete_case385
end Erdos184Work.PureSixLocalFilter1
