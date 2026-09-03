import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_214_0 : CompleteAt 214 0 := by decide +kernel
lemma complete_214_1 : CompleteAt 214 1 := by decide +kernel
lemma complete_214_2 : CompleteAt 214 2 := by decide +kernel
lemma complete_214_3 : CompleteAt 214 3 := by decide +kernel
lemma complete_214_4 : CompleteAt 214 4 := by decide +kernel
lemma complete_case214 : ∀ e0, CompleteAt 214 e0 := by
  intro e0
  fin_cases e0
  · exact complete_214_0
  · exact complete_214_1
  · exact complete_214_2
  · exact complete_214_3
  · exact complete_214_4
#print axioms complete_case214
end Erdos184Work.PureSixLocalFilter1
