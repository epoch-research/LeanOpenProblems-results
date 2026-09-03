import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_163_0 : CompleteAt 163 0 := by decide +kernel
lemma complete_163_1 : CompleteAt 163 1 := by decide +kernel
lemma complete_163_2 : CompleteAt 163 2 := by decide +kernel
lemma complete_163_3 : CompleteAt 163 3 := by decide +kernel
lemma complete_163_4 : CompleteAt 163 4 := by decide +kernel
lemma complete_case163 : ∀ e0, CompleteAt 163 e0 := by
  intro e0
  fin_cases e0
  · exact complete_163_0
  · exact complete_163_1
  · exact complete_163_2
  · exact complete_163_3
  · exact complete_163_4
#print axioms complete_case163
end Erdos184Work.PureSixLocalFilter1
