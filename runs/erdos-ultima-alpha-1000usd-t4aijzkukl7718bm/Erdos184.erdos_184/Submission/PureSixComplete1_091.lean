import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_91_0 : CompleteAt 91 0 := by decide +kernel
lemma complete_91_1 : CompleteAt 91 1 := by decide +kernel
lemma complete_91_2 : CompleteAt 91 2 := by decide +kernel
lemma complete_91_3 : CompleteAt 91 3 := by decide +kernel
lemma complete_91_4 : CompleteAt 91 4 := by decide +kernel
lemma complete_case91 : ∀ e0, CompleteAt 91 e0 := by
  intro e0
  fin_cases e0
  · exact complete_91_0
  · exact complete_91_1
  · exact complete_91_2
  · exact complete_91_3
  · exact complete_91_4
#print axioms complete_case91
end Erdos184Work.PureSixLocalFilter1
