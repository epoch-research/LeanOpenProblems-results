import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_370_0 : CompleteAt 370 0 := by decide +kernel
lemma complete_370_1 : CompleteAt 370 1 := by decide +kernel
lemma complete_370_2 : CompleteAt 370 2 := by decide +kernel
lemma complete_370_3 : CompleteAt 370 3 := by decide +kernel
lemma complete_370_4 : CompleteAt 370 4 := by decide +kernel
lemma complete_case370 : ∀ e0, CompleteAt 370 e0 := by
  intro e0
  fin_cases e0
  · exact complete_370_0
  · exact complete_370_1
  · exact complete_370_2
  · exact complete_370_3
  · exact complete_370_4
#print axioms complete_case370
end Erdos184Work.PureSixLocalFilter1
