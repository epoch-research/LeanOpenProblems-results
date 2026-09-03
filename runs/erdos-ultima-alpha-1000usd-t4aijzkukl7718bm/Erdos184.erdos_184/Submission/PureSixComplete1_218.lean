import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_218_0 : CompleteAt 218 0 := by decide +kernel
lemma complete_218_1 : CompleteAt 218 1 := by decide +kernel
lemma complete_218_2 : CompleteAt 218 2 := by decide +kernel
lemma complete_218_3 : CompleteAt 218 3 := by decide +kernel
lemma complete_218_4 : CompleteAt 218 4 := by decide +kernel
lemma complete_case218 : ∀ e0, CompleteAt 218 e0 := by
  intro e0
  fin_cases e0
  · exact complete_218_0
  · exact complete_218_1
  · exact complete_218_2
  · exact complete_218_3
  · exact complete_218_4
#print axioms complete_case218
end Erdos184Work.PureSixLocalFilter1
