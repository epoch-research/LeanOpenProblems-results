import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_129_0 : CompleteAt 129 0 := by decide +kernel
lemma complete_129_1 : CompleteAt 129 1 := by decide +kernel
lemma complete_129_2 : CompleteAt 129 2 := by decide +kernel
lemma complete_129_3 : CompleteAt 129 3 := by decide +kernel
lemma complete_case129 : ∀ e0, CompleteAt 129 e0 := by
  intro e0
  fin_cases e0
  · exact complete_129_0
  · exact complete_129_1
  · exact complete_129_2
  · exact complete_129_3
#print axioms complete_case129
end Erdos184Work.PureSixLocalFilter0
