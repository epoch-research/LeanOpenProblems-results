import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_123_0 : CompleteAt 123 0 := by decide +kernel
lemma complete_123_1 : CompleteAt 123 1 := by decide +kernel
lemma complete_123_2 : CompleteAt 123 2 := by decide +kernel
lemma complete_123_3 : CompleteAt 123 3 := by decide +kernel
lemma complete_123_4 : CompleteAt 123 4 := by decide +kernel
lemma complete_case123 : ∀ e0, CompleteAt 123 e0 := by
  intro e0
  fin_cases e0
  · exact complete_123_0
  · exact complete_123_1
  · exact complete_123_2
  · exact complete_123_3
  · exact complete_123_4
#print axioms complete_case123
end Erdos184Work.PureSixLocalFilter1
