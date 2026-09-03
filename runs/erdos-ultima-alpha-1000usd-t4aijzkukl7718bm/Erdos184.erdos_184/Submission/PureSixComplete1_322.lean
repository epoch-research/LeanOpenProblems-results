import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_322_0 : CompleteAt 322 0 := by decide +kernel
lemma complete_322_1 : CompleteAt 322 1 := by decide +kernel
lemma complete_322_2 : CompleteAt 322 2 := by decide +kernel
lemma complete_322_3 : CompleteAt 322 3 := by decide +kernel
lemma complete_322_4 : CompleteAt 322 4 := by decide +kernel
lemma complete_case322 : ∀ e0, CompleteAt 322 e0 := by
  intro e0
  fin_cases e0
  · exact complete_322_0
  · exact complete_322_1
  · exact complete_322_2
  · exact complete_322_3
  · exact complete_322_4
#print axioms complete_case322
end Erdos184Work.PureSixLocalFilter1
