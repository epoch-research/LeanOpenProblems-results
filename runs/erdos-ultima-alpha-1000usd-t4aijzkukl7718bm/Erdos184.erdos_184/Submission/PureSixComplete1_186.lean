import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_186_0 : CompleteAt 186 0 := by decide +kernel
lemma complete_186_1 : CompleteAt 186 1 := by decide +kernel
lemma complete_186_2 : CompleteAt 186 2 := by decide +kernel
lemma complete_186_3 : CompleteAt 186 3 := by decide +kernel
lemma complete_186_4 : CompleteAt 186 4 := by decide +kernel
lemma complete_case186 : ∀ e0, CompleteAt 186 e0 := by
  intro e0
  fin_cases e0
  · exact complete_186_0
  · exact complete_186_1
  · exact complete_186_2
  · exact complete_186_3
  · exact complete_186_4
#print axioms complete_case186
end Erdos184Work.PureSixLocalFilter1
