import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_112_0 : CompleteAt 112 0 := by decide +kernel
lemma complete_112_1 : CompleteAt 112 1 := by decide +kernel
lemma complete_112_2 : CompleteAt 112 2 := by decide +kernel
lemma complete_112_3 : CompleteAt 112 3 := by decide +kernel
lemma complete_112_4 : CompleteAt 112 4 := by decide +kernel
lemma complete_case112 : ∀ e0, CompleteAt 112 e0 := by
  intro e0
  fin_cases e0
  · exact complete_112_0
  · exact complete_112_1
  · exact complete_112_2
  · exact complete_112_3
  · exact complete_112_4
#print axioms complete_case112
end Erdos184Work.PureSixLocalFilter1
