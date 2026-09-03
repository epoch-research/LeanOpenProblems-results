import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_223_0 : CompleteAt 223 0 := by decide +kernel
lemma complete_223_1 : CompleteAt 223 1 := by decide +kernel
lemma complete_223_2 : CompleteAt 223 2 := by decide +kernel
lemma complete_223_3 : CompleteAt 223 3 := by decide +kernel
lemma complete_223_4 : CompleteAt 223 4 := by decide +kernel
lemma complete_case223 : ∀ e0, CompleteAt 223 e0 := by
  intro e0
  fin_cases e0
  · exact complete_223_0
  · exact complete_223_1
  · exact complete_223_2
  · exact complete_223_3
  · exact complete_223_4
#print axioms complete_case223
end Erdos184Work.PureSixLocalFilter1
