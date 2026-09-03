import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_148_0 : CompleteAt 148 0 := by decide +kernel
lemma complete_148_1 : CompleteAt 148 1 := by decide +kernel
lemma complete_148_2 : CompleteAt 148 2 := by decide +kernel
lemma complete_148_3 : CompleteAt 148 3 := by decide +kernel
lemma complete_case148 : ∀ e0, CompleteAt 148 e0 := by
  intro e0
  fin_cases e0
  · exact complete_148_0
  · exact complete_148_1
  · exact complete_148_2
  · exact complete_148_3
#print axioms complete_case148
end Erdos184Work.PureSixLocalFilter0
