import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_288_0 : CompleteAt 288 0 := by decide +kernel
lemma complete_288_1 : CompleteAt 288 1 := by decide +kernel
lemma complete_288_2 : CompleteAt 288 2 := by decide +kernel
lemma complete_288_3 : CompleteAt 288 3 := by decide +kernel
lemma complete_288_4 : CompleteAt 288 4 := by decide +kernel
lemma complete_case288 : ∀ e0, CompleteAt 288 e0 := by
  intro e0
  fin_cases e0
  · exact complete_288_0
  · exact complete_288_1
  · exact complete_288_2
  · exact complete_288_3
  · exact complete_288_4
#print axioms complete_case288
end Erdos184Work.PureSixLocalFilter1
