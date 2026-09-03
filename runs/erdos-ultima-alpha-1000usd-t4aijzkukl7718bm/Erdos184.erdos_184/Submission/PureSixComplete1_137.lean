import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_137_0 : CompleteAt 137 0 := by decide +kernel
lemma complete_137_1 : CompleteAt 137 1 := by decide +kernel
lemma complete_137_2 : CompleteAt 137 2 := by decide +kernel
lemma complete_137_3 : CompleteAt 137 3 := by decide +kernel
lemma complete_137_4 : CompleteAt 137 4 := by decide +kernel
lemma complete_case137 : ∀ e0, CompleteAt 137 e0 := by
  intro e0
  fin_cases e0
  · exact complete_137_0
  · exact complete_137_1
  · exact complete_137_2
  · exact complete_137_3
  · exact complete_137_4
#print axioms complete_case137
end Erdos184Work.PureSixLocalFilter1
