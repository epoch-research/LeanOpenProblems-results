import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_344_0 : CompleteAt 344 0 := by decide +kernel
lemma complete_344_1 : CompleteAt 344 1 := by decide +kernel
lemma complete_344_2 : CompleteAt 344 2 := by decide +kernel
lemma complete_344_3 : CompleteAt 344 3 := by decide +kernel
lemma complete_344_4 : CompleteAt 344 4 := by decide +kernel
lemma complete_case344 : ∀ e0, CompleteAt 344 e0 := by
  intro e0
  fin_cases e0
  · exact complete_344_0
  · exact complete_344_1
  · exact complete_344_2
  · exact complete_344_3
  · exact complete_344_4
#print axioms complete_case344
end Erdos184Work.PureSixLocalFilter1
