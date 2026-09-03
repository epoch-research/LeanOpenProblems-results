import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_252_0 : CompleteAt 252 0 := by decide +kernel
lemma complete_252_1 : CompleteAt 252 1 := by decide +kernel
lemma complete_252_2 : CompleteAt 252 2 := by decide +kernel
lemma complete_252_3 : CompleteAt 252 3 := by decide +kernel
lemma complete_252_4 : CompleteAt 252 4 := by decide +kernel
lemma complete_case252 : ∀ e0, CompleteAt 252 e0 := by
  intro e0
  fin_cases e0
  · exact complete_252_0
  · exact complete_252_1
  · exact complete_252_2
  · exact complete_252_3
  · exact complete_252_4
#print axioms complete_case252
end Erdos184Work.PureSixLocalFilter1
