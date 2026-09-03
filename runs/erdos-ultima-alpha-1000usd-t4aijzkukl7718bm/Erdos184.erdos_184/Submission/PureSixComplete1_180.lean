import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_180_0 : CompleteAt 180 0 := by decide +kernel
lemma complete_180_1 : CompleteAt 180 1 := by decide +kernel
lemma complete_180_2 : CompleteAt 180 2 := by decide +kernel
lemma complete_180_3 : CompleteAt 180 3 := by decide +kernel
lemma complete_180_4 : CompleteAt 180 4 := by decide +kernel
lemma complete_case180 : ∀ e0, CompleteAt 180 e0 := by
  intro e0
  fin_cases e0
  · exact complete_180_0
  · exact complete_180_1
  · exact complete_180_2
  · exact complete_180_3
  · exact complete_180_4
#print axioms complete_case180
end Erdos184Work.PureSixLocalFilter1
