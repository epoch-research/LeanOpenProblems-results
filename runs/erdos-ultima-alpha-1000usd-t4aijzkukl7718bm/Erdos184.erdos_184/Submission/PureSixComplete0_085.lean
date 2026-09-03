import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_85_0 : CompleteAt 85 0 := by decide +kernel
lemma complete_85_1 : CompleteAt 85 1 := by decide +kernel
lemma complete_85_2 : CompleteAt 85 2 := by decide +kernel
lemma complete_85_3 : CompleteAt 85 3 := by decide +kernel
lemma complete_case85 : ∀ e0, CompleteAt 85 e0 := by
  intro e0
  fin_cases e0
  · exact complete_85_0
  · exact complete_85_1
  · exact complete_85_2
  · exact complete_85_3
#print axioms complete_case85
end Erdos184Work.PureSixLocalFilter0
