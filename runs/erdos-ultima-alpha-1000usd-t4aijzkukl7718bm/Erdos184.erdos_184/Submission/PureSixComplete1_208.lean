import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_208_0 : CompleteAt 208 0 := by decide +kernel
lemma complete_208_1 : CompleteAt 208 1 := by decide +kernel
lemma complete_208_2 : CompleteAt 208 2 := by decide +kernel
lemma complete_208_3 : CompleteAt 208 3 := by decide +kernel
lemma complete_208_4 : CompleteAt 208 4 := by decide +kernel
lemma complete_case208 : ∀ e0, CompleteAt 208 e0 := by
  intro e0
  fin_cases e0
  · exact complete_208_0
  · exact complete_208_1
  · exact complete_208_2
  · exact complete_208_3
  · exact complete_208_4
#print axioms complete_case208
end Erdos184Work.PureSixLocalFilter1
