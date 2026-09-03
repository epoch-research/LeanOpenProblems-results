import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_279_0 : CompleteAt 279 0 := by decide +kernel
lemma complete_279_1 : CompleteAt 279 1 := by decide +kernel
lemma complete_279_2 : CompleteAt 279 2 := by decide +kernel
lemma complete_279_3 : CompleteAt 279 3 := by decide +kernel
lemma complete_279_4 : CompleteAt 279 4 := by decide +kernel
lemma complete_case279 : ∀ e0, CompleteAt 279 e0 := by
  intro e0
  fin_cases e0
  · exact complete_279_0
  · exact complete_279_1
  · exact complete_279_2
  · exact complete_279_3
  · exact complete_279_4
#print axioms complete_case279
end Erdos184Work.PureSixLocalFilter1
