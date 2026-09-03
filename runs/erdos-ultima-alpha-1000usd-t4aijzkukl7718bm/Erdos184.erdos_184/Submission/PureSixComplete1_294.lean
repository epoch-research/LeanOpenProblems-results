import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_294_0 : CompleteAt 294 0 := by decide +kernel
lemma complete_294_1 : CompleteAt 294 1 := by decide +kernel
lemma complete_294_2 : CompleteAt 294 2 := by decide +kernel
lemma complete_294_3 : CompleteAt 294 3 := by decide +kernel
lemma complete_294_4 : CompleteAt 294 4 := by decide +kernel
lemma complete_case294 : ∀ e0, CompleteAt 294 e0 := by
  intro e0
  fin_cases e0
  · exact complete_294_0
  · exact complete_294_1
  · exact complete_294_2
  · exact complete_294_3
  · exact complete_294_4
#print axioms complete_case294
end Erdos184Work.PureSixLocalFilter1
