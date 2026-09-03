import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_264_0 : CompleteAt 264 0 := by decide +kernel
lemma complete_264_1 : CompleteAt 264 1 := by decide +kernel
lemma complete_264_2 : CompleteAt 264 2 := by decide +kernel
lemma complete_264_3 : CompleteAt 264 3 := by decide +kernel
lemma complete_264_4 : CompleteAt 264 4 := by decide +kernel
lemma complete_case264 : ∀ e0, CompleteAt 264 e0 := by
  intro e0
  fin_cases e0
  · exact complete_264_0
  · exact complete_264_1
  · exact complete_264_2
  · exact complete_264_3
  · exact complete_264_4
#print axioms complete_case264
end Erdos184Work.PureSixLocalFilter1
