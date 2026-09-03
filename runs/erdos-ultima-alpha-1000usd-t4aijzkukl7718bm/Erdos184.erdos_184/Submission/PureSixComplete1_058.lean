import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_58_0 : CompleteAt 58 0 := by decide +kernel
lemma complete_58_1 : CompleteAt 58 1 := by decide +kernel
lemma complete_58_2 : CompleteAt 58 2 := by decide +kernel
lemma complete_58_3 : CompleteAt 58 3 := by decide +kernel
lemma complete_58_4 : CompleteAt 58 4 := by decide +kernel
lemma complete_case58 : ∀ e0, CompleteAt 58 e0 := by
  intro e0
  fin_cases e0
  · exact complete_58_0
  · exact complete_58_1
  · exact complete_58_2
  · exact complete_58_3
  · exact complete_58_4
#print axioms complete_case58
end Erdos184Work.PureSixLocalFilter1
