import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_172_0 : CompleteAt 172 0 := by decide +kernel
lemma complete_172_1 : CompleteAt 172 1 := by decide +kernel
lemma complete_172_2 : CompleteAt 172 2 := by decide +kernel
lemma complete_172_3 : CompleteAt 172 3 := by decide +kernel
lemma complete_172_4 : CompleteAt 172 4 := by decide +kernel
lemma complete_case172 : ∀ e0, CompleteAt 172 e0 := by
  intro e0
  fin_cases e0
  · exact complete_172_0
  · exact complete_172_1
  · exact complete_172_2
  · exact complete_172_3
  · exact complete_172_4
#print axioms complete_case172
end Erdos184Work.PureSixLocalFilter1
