import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_49_0 : CompleteAt 49 0 := by decide +kernel
lemma complete_49_1 : CompleteAt 49 1 := by decide +kernel
lemma complete_49_2 : CompleteAt 49 2 := by decide +kernel
lemma complete_49_3 : CompleteAt 49 3 := by decide +kernel
lemma complete_case49 : ∀ e0, CompleteAt 49 e0 := by
  intro e0
  fin_cases e0
  · exact complete_49_0
  · exact complete_49_1
  · exact complete_49_2
  · exact complete_49_3
#print axioms complete_case49
end Erdos184Work.PureSixLocalFilter0
