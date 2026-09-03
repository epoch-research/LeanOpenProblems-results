import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_320_0 : CompleteAt 320 0 := by decide +kernel
lemma complete_320_1 : CompleteAt 320 1 := by decide +kernel
lemma complete_320_2 : CompleteAt 320 2 := by decide +kernel
lemma complete_320_3 : CompleteAt 320 3 := by decide +kernel
lemma complete_320_4 : CompleteAt 320 4 := by decide +kernel
lemma complete_case320 : ∀ e0, CompleteAt 320 e0 := by
  intro e0
  fin_cases e0
  · exact complete_320_0
  · exact complete_320_1
  · exact complete_320_2
  · exact complete_320_3
  · exact complete_320_4
#print axioms complete_case320
end Erdos184Work.PureSixLocalFilter1
