import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_140_0 : CompleteAt 140 0 := by decide +kernel
lemma complete_140_1 : CompleteAt 140 1 := by decide +kernel
lemma complete_140_2 : CompleteAt 140 2 := by decide +kernel
lemma complete_140_3 : CompleteAt 140 3 := by decide +kernel
lemma complete_case140 : ∀ e0, CompleteAt 140 e0 := by
  intro e0
  fin_cases e0
  · exact complete_140_0
  · exact complete_140_1
  · exact complete_140_2
  · exact complete_140_3
#print axioms complete_case140
end Erdos184Work.PureSixLocalFilter0
