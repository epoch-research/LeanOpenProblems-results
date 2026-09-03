import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_158_0 : CompleteAt 158 0 := by decide +kernel
lemma complete_158_1 : CompleteAt 158 1 := by decide +kernel
lemma complete_158_2 : CompleteAt 158 2 := by decide +kernel
lemma complete_158_3 : CompleteAt 158 3 := by decide +kernel
lemma complete_158_4 : CompleteAt 158 4 := by decide +kernel
lemma complete_case158 : ∀ e0, CompleteAt 158 e0 := by
  intro e0
  fin_cases e0
  · exact complete_158_0
  · exact complete_158_1
  · exact complete_158_2
  · exact complete_158_3
  · exact complete_158_4
#print axioms complete_case158
end Erdos184Work.PureSixLocalFilter1
