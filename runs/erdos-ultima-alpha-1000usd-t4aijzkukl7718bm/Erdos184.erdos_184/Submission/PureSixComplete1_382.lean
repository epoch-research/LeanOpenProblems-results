import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_382_0 : CompleteAt 382 0 := by decide +kernel
lemma complete_382_1 : CompleteAt 382 1 := by decide +kernel
lemma complete_382_2 : CompleteAt 382 2 := by decide +kernel
lemma complete_382_3 : CompleteAt 382 3 := by decide +kernel
lemma complete_382_4 : CompleteAt 382 4 := by decide +kernel
lemma complete_case382 : ∀ e0, CompleteAt 382 e0 := by
  intro e0
  fin_cases e0
  · exact complete_382_0
  · exact complete_382_1
  · exact complete_382_2
  · exact complete_382_3
  · exact complete_382_4
#print axioms complete_case382
end Erdos184Work.PureSixLocalFilter1
