import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_136_0 : CompleteAt 136 0 := by decide +kernel
lemma complete_136_1 : CompleteAt 136 1 := by decide +kernel
lemma complete_136_2 : CompleteAt 136 2 := by decide +kernel
lemma complete_136_3 : CompleteAt 136 3 := by decide +kernel
lemma complete_136_4 : CompleteAt 136 4 := by decide +kernel
lemma complete_case136 : ∀ e0, CompleteAt 136 e0 := by
  intro e0
  fin_cases e0
  · exact complete_136_0
  · exact complete_136_1
  · exact complete_136_2
  · exact complete_136_3
  · exact complete_136_4
#print axioms complete_case136
end Erdos184Work.PureSixLocalFilter1
