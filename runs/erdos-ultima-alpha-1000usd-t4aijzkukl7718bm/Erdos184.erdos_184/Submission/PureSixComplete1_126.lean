import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_126_0 : CompleteAt 126 0 := by decide +kernel
lemma complete_126_1 : CompleteAt 126 1 := by decide +kernel
lemma complete_126_2 : CompleteAt 126 2 := by decide +kernel
lemma complete_126_3 : CompleteAt 126 3 := by decide +kernel
lemma complete_126_4 : CompleteAt 126 4 := by decide +kernel
lemma complete_case126 : ∀ e0, CompleteAt 126 e0 := by
  intro e0
  fin_cases e0
  · exact complete_126_0
  · exact complete_126_1
  · exact complete_126_2
  · exact complete_126_3
  · exact complete_126_4
#print axioms complete_case126
end Erdos184Work.PureSixLocalFilter1
