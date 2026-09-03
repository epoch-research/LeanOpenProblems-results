import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_238_0 : CompleteAt 238 0 := by decide +kernel
lemma complete_238_1 : CompleteAt 238 1 := by decide +kernel
lemma complete_238_2 : CompleteAt 238 2 := by decide +kernel
lemma complete_238_3 : CompleteAt 238 3 := by decide +kernel
lemma complete_238_4 : CompleteAt 238 4 := by decide +kernel
lemma complete_case238 : ∀ e0, CompleteAt 238 e0 := by
  intro e0
  fin_cases e0
  · exact complete_238_0
  · exact complete_238_1
  · exact complete_238_2
  · exact complete_238_3
  · exact complete_238_4
#print axioms complete_case238
end Erdos184Work.PureSixLocalFilter1
