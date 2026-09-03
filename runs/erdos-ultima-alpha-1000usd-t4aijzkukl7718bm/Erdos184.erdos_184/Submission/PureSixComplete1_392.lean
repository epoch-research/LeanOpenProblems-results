import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_392_0 : CompleteAt 392 0 := by decide +kernel
lemma complete_392_1 : CompleteAt 392 1 := by decide +kernel
lemma complete_392_2 : CompleteAt 392 2 := by decide +kernel
lemma complete_392_3 : CompleteAt 392 3 := by decide +kernel
lemma complete_392_4 : CompleteAt 392 4 := by decide +kernel
lemma complete_case392 : ∀ e0, CompleteAt 392 e0 := by
  intro e0
  fin_cases e0
  · exact complete_392_0
  · exact complete_392_1
  · exact complete_392_2
  · exact complete_392_3
  · exact complete_392_4
#print axioms complete_case392
end Erdos184Work.PureSixLocalFilter1
