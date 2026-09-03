import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_262_0 : CompleteAt 262 0 := by decide +kernel
lemma complete_262_1 : CompleteAt 262 1 := by decide +kernel
lemma complete_262_2 : CompleteAt 262 2 := by decide +kernel
lemma complete_262_3 : CompleteAt 262 3 := by decide +kernel
lemma complete_262_4 : CompleteAt 262 4 := by decide +kernel
lemma complete_case262 : ∀ e0, CompleteAt 262 e0 := by
  intro e0
  fin_cases e0
  · exact complete_262_0
  · exact complete_262_1
  · exact complete_262_2
  · exact complete_262_3
  · exact complete_262_4
#print axioms complete_case262
end Erdos184Work.PureSixLocalFilter1
