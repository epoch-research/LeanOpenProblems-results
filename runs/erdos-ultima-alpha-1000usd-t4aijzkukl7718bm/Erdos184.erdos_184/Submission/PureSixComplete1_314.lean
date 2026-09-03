import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_314_0 : CompleteAt 314 0 := by decide +kernel
lemma complete_314_1 : CompleteAt 314 1 := by decide +kernel
lemma complete_314_2 : CompleteAt 314 2 := by decide +kernel
lemma complete_314_3 : CompleteAt 314 3 := by decide +kernel
lemma complete_314_4 : CompleteAt 314 4 := by decide +kernel
lemma complete_case314 : ∀ e0, CompleteAt 314 e0 := by
  intro e0
  fin_cases e0
  · exact complete_314_0
  · exact complete_314_1
  · exact complete_314_2
  · exact complete_314_3
  · exact complete_314_4
#print axioms complete_case314
end Erdos184Work.PureSixLocalFilter1
