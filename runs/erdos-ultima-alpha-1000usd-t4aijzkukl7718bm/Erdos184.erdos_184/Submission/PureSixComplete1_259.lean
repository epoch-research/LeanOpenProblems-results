import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_259_0 : CompleteAt 259 0 := by decide +kernel
lemma complete_259_1 : CompleteAt 259 1 := by decide +kernel
lemma complete_259_2 : CompleteAt 259 2 := by decide +kernel
lemma complete_259_3 : CompleteAt 259 3 := by decide +kernel
lemma complete_259_4 : CompleteAt 259 4 := by decide +kernel
lemma complete_case259 : ∀ e0, CompleteAt 259 e0 := by
  intro e0
  fin_cases e0
  · exact complete_259_0
  · exact complete_259_1
  · exact complete_259_2
  · exact complete_259_3
  · exact complete_259_4
#print axioms complete_case259
end Erdos184Work.PureSixLocalFilter1
