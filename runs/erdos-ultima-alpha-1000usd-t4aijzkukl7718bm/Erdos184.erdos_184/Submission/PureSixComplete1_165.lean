import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_165_0 : CompleteAt 165 0 := by decide +kernel
lemma complete_165_1 : CompleteAt 165 1 := by decide +kernel
lemma complete_165_2 : CompleteAt 165 2 := by decide +kernel
lemma complete_165_3 : CompleteAt 165 3 := by decide +kernel
lemma complete_165_4 : CompleteAt 165 4 := by decide +kernel
lemma complete_case165 : ∀ e0, CompleteAt 165 e0 := by
  intro e0
  fin_cases e0
  · exact complete_165_0
  · exact complete_165_1
  · exact complete_165_2
  · exact complete_165_3
  · exact complete_165_4
#print axioms complete_case165
end Erdos184Work.PureSixLocalFilter1
