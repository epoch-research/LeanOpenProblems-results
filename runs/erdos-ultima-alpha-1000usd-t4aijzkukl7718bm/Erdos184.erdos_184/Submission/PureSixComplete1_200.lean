import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_200_0 : CompleteAt 200 0 := by decide +kernel
lemma complete_200_1 : CompleteAt 200 1 := by decide +kernel
lemma complete_200_2 : CompleteAt 200 2 := by decide +kernel
lemma complete_200_3 : CompleteAt 200 3 := by decide +kernel
lemma complete_200_4 : CompleteAt 200 4 := by decide +kernel
lemma complete_case200 : ∀ e0, CompleteAt 200 e0 := by
  intro e0
  fin_cases e0
  · exact complete_200_0
  · exact complete_200_1
  · exact complete_200_2
  · exact complete_200_3
  · exact complete_200_4
#print axioms complete_case200
end Erdos184Work.PureSixLocalFilter1
