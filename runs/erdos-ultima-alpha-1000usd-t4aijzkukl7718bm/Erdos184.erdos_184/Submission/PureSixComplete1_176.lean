import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_176_0 : CompleteAt 176 0 := by decide +kernel
lemma complete_176_1 : CompleteAt 176 1 := by decide +kernel
lemma complete_176_2 : CompleteAt 176 2 := by decide +kernel
lemma complete_176_3 : CompleteAt 176 3 := by decide +kernel
lemma complete_176_4 : CompleteAt 176 4 := by decide +kernel
lemma complete_case176 : ∀ e0, CompleteAt 176 e0 := by
  intro e0
  fin_cases e0
  · exact complete_176_0
  · exact complete_176_1
  · exact complete_176_2
  · exact complete_176_3
  · exact complete_176_4
#print axioms complete_case176
end Erdos184Work.PureSixLocalFilter1
