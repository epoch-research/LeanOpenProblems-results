import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_311_0 : CompleteAt 311 0 := by decide +kernel
lemma complete_311_1 : CompleteAt 311 1 := by decide +kernel
lemma complete_311_2 : CompleteAt 311 2 := by decide +kernel
lemma complete_311_3 : CompleteAt 311 3 := by decide +kernel
lemma complete_311_4 : CompleteAt 311 4 := by decide +kernel
lemma complete_case311 : ∀ e0, CompleteAt 311 e0 := by
  intro e0
  fin_cases e0
  · exact complete_311_0
  · exact complete_311_1
  · exact complete_311_2
  · exact complete_311_3
  · exact complete_311_4
#print axioms complete_case311
end Erdos184Work.PureSixLocalFilter1
