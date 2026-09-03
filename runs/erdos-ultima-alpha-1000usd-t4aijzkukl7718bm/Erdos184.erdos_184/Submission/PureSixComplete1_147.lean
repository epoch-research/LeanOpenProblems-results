import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_147_0 : CompleteAt 147 0 := by decide +kernel
lemma complete_147_1 : CompleteAt 147 1 := by decide +kernel
lemma complete_147_2 : CompleteAt 147 2 := by decide +kernel
lemma complete_147_3 : CompleteAt 147 3 := by decide +kernel
lemma complete_147_4 : CompleteAt 147 4 := by decide +kernel
lemma complete_case147 : ∀ e0, CompleteAt 147 e0 := by
  intro e0
  fin_cases e0
  · exact complete_147_0
  · exact complete_147_1
  · exact complete_147_2
  · exact complete_147_3
  · exact complete_147_4
#print axioms complete_case147
end Erdos184Work.PureSixLocalFilter1
