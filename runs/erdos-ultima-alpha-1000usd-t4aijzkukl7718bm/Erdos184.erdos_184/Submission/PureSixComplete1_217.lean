import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_217_0 : CompleteAt 217 0 := by decide +kernel
lemma complete_217_1 : CompleteAt 217 1 := by decide +kernel
lemma complete_217_2 : CompleteAt 217 2 := by decide +kernel
lemma complete_217_3 : CompleteAt 217 3 := by decide +kernel
lemma complete_217_4 : CompleteAt 217 4 := by decide +kernel
lemma complete_case217 : ∀ e0, CompleteAt 217 e0 := by
  intro e0
  fin_cases e0
  · exact complete_217_0
  · exact complete_217_1
  · exact complete_217_2
  · exact complete_217_3
  · exact complete_217_4
#print axioms complete_case217
end Erdos184Work.PureSixLocalFilter1
