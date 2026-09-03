import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_135_0 : CompleteAt 135 0 := by decide +kernel
lemma complete_135_1 : CompleteAt 135 1 := by decide +kernel
lemma complete_135_2 : CompleteAt 135 2 := by decide +kernel
lemma complete_135_3 : CompleteAt 135 3 := by decide +kernel
lemma complete_135_4 : CompleteAt 135 4 := by decide +kernel
lemma complete_case135 : ∀ e0, CompleteAt 135 e0 := by
  intro e0
  fin_cases e0
  · exact complete_135_0
  · exact complete_135_1
  · exact complete_135_2
  · exact complete_135_3
  · exact complete_135_4
#print axioms complete_case135
end Erdos184Work.PureSixLocalFilter1
