import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_106_0 : CompleteAt 106 0 := by decide +kernel
lemma complete_106_1 : CompleteAt 106 1 := by decide +kernel
lemma complete_106_2 : CompleteAt 106 2 := by decide +kernel
lemma complete_106_3 : CompleteAt 106 3 := by decide +kernel
lemma complete_case106 : ∀ e0, CompleteAt 106 e0 := by
  intro e0
  fin_cases e0
  · exact complete_106_0
  · exact complete_106_1
  · exact complete_106_2
  · exact complete_106_3
#print axioms complete_case106
end Erdos184Work.PureSixLocalFilter0
