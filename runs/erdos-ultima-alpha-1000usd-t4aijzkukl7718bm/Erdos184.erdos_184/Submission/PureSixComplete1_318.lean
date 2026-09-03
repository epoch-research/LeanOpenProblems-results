import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_318_0 : CompleteAt 318 0 := by decide +kernel
lemma complete_318_1 : CompleteAt 318 1 := by decide +kernel
lemma complete_318_2 : CompleteAt 318 2 := by decide +kernel
lemma complete_318_3 : CompleteAt 318 3 := by decide +kernel
lemma complete_318_4 : CompleteAt 318 4 := by decide +kernel
lemma complete_case318 : ∀ e0, CompleteAt 318 e0 := by
  intro e0
  fin_cases e0
  · exact complete_318_0
  · exact complete_318_1
  · exact complete_318_2
  · exact complete_318_3
  · exact complete_318_4
#print axioms complete_case318
end Erdos184Work.PureSixLocalFilter1
