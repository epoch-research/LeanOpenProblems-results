import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_161_0 : CompleteAt 161 0 := by decide +kernel
lemma complete_161_1 : CompleteAt 161 1 := by decide +kernel
lemma complete_161_2 : CompleteAt 161 2 := by decide +kernel
lemma complete_161_3 : CompleteAt 161 3 := by decide +kernel
lemma complete_161_4 : CompleteAt 161 4 := by decide +kernel
lemma complete_case161 : ∀ e0, CompleteAt 161 e0 := by
  intro e0
  fin_cases e0
  · exact complete_161_0
  · exact complete_161_1
  · exact complete_161_2
  · exact complete_161_3
  · exact complete_161_4
#print axioms complete_case161
end Erdos184Work.PureSixLocalFilter1
