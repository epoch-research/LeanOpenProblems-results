import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_302_0 : CompleteAt 302 0 := by decide +kernel
lemma complete_302_1 : CompleteAt 302 1 := by decide +kernel
lemma complete_302_2 : CompleteAt 302 2 := by decide +kernel
lemma complete_302_3 : CompleteAt 302 3 := by decide +kernel
lemma complete_302_4 : CompleteAt 302 4 := by decide +kernel
lemma complete_case302 : ∀ e0, CompleteAt 302 e0 := by
  intro e0
  fin_cases e0
  · exact complete_302_0
  · exact complete_302_1
  · exact complete_302_2
  · exact complete_302_3
  · exact complete_302_4
#print axioms complete_case302
end Erdos184Work.PureSixLocalFilter1
