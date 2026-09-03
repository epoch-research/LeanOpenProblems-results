import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_154_0 : CompleteAt 154 0 := by decide +kernel
lemma complete_154_1 : CompleteAt 154 1 := by decide +kernel
lemma complete_154_2 : CompleteAt 154 2 := by decide +kernel
lemma complete_154_3 : CompleteAt 154 3 := by decide +kernel
lemma complete_case154 : ∀ e0, CompleteAt 154 e0 := by
  intro e0
  fin_cases e0
  · exact complete_154_0
  · exact complete_154_1
  · exact complete_154_2
  · exact complete_154_3
#print axioms complete_case154
end Erdos184Work.PureSixLocalFilter0
