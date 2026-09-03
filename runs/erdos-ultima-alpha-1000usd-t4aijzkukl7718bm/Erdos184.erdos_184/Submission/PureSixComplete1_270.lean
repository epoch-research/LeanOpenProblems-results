import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_270_0 : CompleteAt 270 0 := by decide +kernel
lemma complete_270_1 : CompleteAt 270 1 := by decide +kernel
lemma complete_270_2 : CompleteAt 270 2 := by decide +kernel
lemma complete_270_3 : CompleteAt 270 3 := by decide +kernel
lemma complete_270_4 : CompleteAt 270 4 := by decide +kernel
lemma complete_case270 : ∀ e0, CompleteAt 270 e0 := by
  intro e0
  fin_cases e0
  · exact complete_270_0
  · exact complete_270_1
  · exact complete_270_2
  · exact complete_270_3
  · exact complete_270_4
#print axioms complete_case270
end Erdos184Work.PureSixLocalFilter1
