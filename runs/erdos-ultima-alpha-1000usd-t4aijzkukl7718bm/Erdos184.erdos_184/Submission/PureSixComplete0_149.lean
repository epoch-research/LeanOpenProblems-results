import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_149_0 : CompleteAt 149 0 := by decide +kernel
lemma complete_149_1 : CompleteAt 149 1 := by decide +kernel
lemma complete_149_2 : CompleteAt 149 2 := by decide +kernel
lemma complete_149_3 : CompleteAt 149 3 := by decide +kernel
lemma complete_case149 : ∀ e0, CompleteAt 149 e0 := by
  intro e0
  fin_cases e0
  · exact complete_149_0
  · exact complete_149_1
  · exact complete_149_2
  · exact complete_149_3
#print axioms complete_case149
end Erdos184Work.PureSixLocalFilter0
