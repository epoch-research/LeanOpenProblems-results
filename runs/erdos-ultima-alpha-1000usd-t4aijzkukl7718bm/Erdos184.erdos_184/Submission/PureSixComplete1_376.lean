import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_376_0 : CompleteAt 376 0 := by decide +kernel
lemma complete_376_1 : CompleteAt 376 1 := by decide +kernel
lemma complete_376_2 : CompleteAt 376 2 := by decide +kernel
lemma complete_376_3 : CompleteAt 376 3 := by decide +kernel
lemma complete_376_4 : CompleteAt 376 4 := by decide +kernel
lemma complete_case376 : ∀ e0, CompleteAt 376 e0 := by
  intro e0
  fin_cases e0
  · exact complete_376_0
  · exact complete_376_1
  · exact complete_376_2
  · exact complete_376_3
  · exact complete_376_4
#print axioms complete_case376
end Erdos184Work.PureSixLocalFilter1
