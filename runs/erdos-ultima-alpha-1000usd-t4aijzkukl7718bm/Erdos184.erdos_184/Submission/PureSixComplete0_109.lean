import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_109_0 : CompleteAt 109 0 := by decide +kernel
lemma complete_109_1 : CompleteAt 109 1 := by decide +kernel
lemma complete_109_2 : CompleteAt 109 2 := by decide +kernel
lemma complete_109_3 : CompleteAt 109 3 := by decide +kernel
lemma complete_case109 : ∀ e0, CompleteAt 109 e0 := by
  intro e0
  fin_cases e0
  · exact complete_109_0
  · exact complete_109_1
  · exact complete_109_2
  · exact complete_109_3
#print axioms complete_case109
end Erdos184Work.PureSixLocalFilter0
