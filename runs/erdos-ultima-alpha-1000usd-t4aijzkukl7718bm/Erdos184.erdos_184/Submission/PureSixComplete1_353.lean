import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_353_0 : CompleteAt 353 0 := by decide +kernel
lemma complete_353_1 : CompleteAt 353 1 := by decide +kernel
lemma complete_353_2 : CompleteAt 353 2 := by decide +kernel
lemma complete_353_3 : CompleteAt 353 3 := by decide +kernel
lemma complete_353_4 : CompleteAt 353 4 := by decide +kernel
lemma complete_case353 : ∀ e0, CompleteAt 353 e0 := by
  intro e0
  fin_cases e0
  · exact complete_353_0
  · exact complete_353_1
  · exact complete_353_2
  · exact complete_353_3
  · exact complete_353_4
#print axioms complete_case353
end Erdos184Work.PureSixLocalFilter1
