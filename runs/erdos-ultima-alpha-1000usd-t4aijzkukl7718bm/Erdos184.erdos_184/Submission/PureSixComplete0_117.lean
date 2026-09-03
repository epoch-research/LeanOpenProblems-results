import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_117_0 : CompleteAt 117 0 := by decide +kernel
lemma complete_117_1 : CompleteAt 117 1 := by decide +kernel
lemma complete_117_2 : CompleteAt 117 2 := by decide +kernel
lemma complete_117_3 : CompleteAt 117 3 := by decide +kernel
lemma complete_case117 : ∀ e0, CompleteAt 117 e0 := by
  intro e0
  fin_cases e0
  · exact complete_117_0
  · exact complete_117_1
  · exact complete_117_2
  · exact complete_117_3
#print axioms complete_case117
end Erdos184Work.PureSixLocalFilter0
