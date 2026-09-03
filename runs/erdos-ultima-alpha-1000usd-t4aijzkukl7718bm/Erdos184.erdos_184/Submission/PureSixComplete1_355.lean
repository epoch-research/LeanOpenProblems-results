import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_355_0 : CompleteAt 355 0 := by decide +kernel
lemma complete_355_1 : CompleteAt 355 1 := by decide +kernel
lemma complete_355_2 : CompleteAt 355 2 := by decide +kernel
lemma complete_355_3 : CompleteAt 355 3 := by decide +kernel
lemma complete_355_4 : CompleteAt 355 4 := by decide +kernel
lemma complete_case355 : ∀ e0, CompleteAt 355 e0 := by
  intro e0
  fin_cases e0
  · exact complete_355_0
  · exact complete_355_1
  · exact complete_355_2
  · exact complete_355_3
  · exact complete_355_4
#print axioms complete_case355
end Erdos184Work.PureSixLocalFilter1
