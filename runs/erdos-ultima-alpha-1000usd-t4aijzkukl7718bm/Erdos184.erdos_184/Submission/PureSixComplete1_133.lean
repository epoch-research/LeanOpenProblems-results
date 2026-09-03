import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_133_0 : CompleteAt 133 0 := by decide +kernel
lemma complete_133_1 : CompleteAt 133 1 := by decide +kernel
lemma complete_133_2 : CompleteAt 133 2 := by decide +kernel
lemma complete_133_3 : CompleteAt 133 3 := by decide +kernel
lemma complete_133_4 : CompleteAt 133 4 := by decide +kernel
lemma complete_case133 : ∀ e0, CompleteAt 133 e0 := by
  intro e0
  fin_cases e0
  · exact complete_133_0
  · exact complete_133_1
  · exact complete_133_2
  · exact complete_133_3
  · exact complete_133_4
#print axioms complete_case133
end Erdos184Work.PureSixLocalFilter1
