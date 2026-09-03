import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_152_0 : CompleteAt 152 0 := by decide +kernel
lemma complete_152_1 : CompleteAt 152 1 := by decide +kernel
lemma complete_152_2 : CompleteAt 152 2 := by decide +kernel
lemma complete_152_3 : CompleteAt 152 3 := by decide +kernel
lemma complete_case152 : ∀ e0, CompleteAt 152 e0 := by
  intro e0
  fin_cases e0
  · exact complete_152_0
  · exact complete_152_1
  · exact complete_152_2
  · exact complete_152_3
#print axioms complete_case152
end Erdos184Work.PureSixLocalFilter0
