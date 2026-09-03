import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_255_0 : CompleteAt 255 0 := by decide +kernel
lemma complete_255_1 : CompleteAt 255 1 := by decide +kernel
lemma complete_255_2 : CompleteAt 255 2 := by decide +kernel
lemma complete_255_3 : CompleteAt 255 3 := by decide +kernel
lemma complete_255_4 : CompleteAt 255 4 := by decide +kernel
lemma complete_case255 : ∀ e0, CompleteAt 255 e0 := by
  intro e0
  fin_cases e0
  · exact complete_255_0
  · exact complete_255_1
  · exact complete_255_2
  · exact complete_255_3
  · exact complete_255_4
#print axioms complete_case255
end Erdos184Work.PureSixLocalFilter1
