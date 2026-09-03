import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_42_0 : CompleteAt 42 0 := by decide +kernel
lemma complete_42_1 : CompleteAt 42 1 := by decide +kernel
lemma complete_42_2 : CompleteAt 42 2 := by decide +kernel
lemma complete_42_3 : CompleteAt 42 3 := by decide +kernel
lemma complete_case42 : ∀ e0, CompleteAt 42 e0 := by
  intro e0
  fin_cases e0
  · exact complete_42_0
  · exact complete_42_1
  · exact complete_42_2
  · exact complete_42_3
#print axioms complete_case42
end Erdos184Work.PureSixLocalFilter0
