import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_260_0 : CompleteAt 260 0 := by decide +kernel
lemma complete_260_1 : CompleteAt 260 1 := by decide +kernel
lemma complete_260_2 : CompleteAt 260 2 := by decide +kernel
lemma complete_260_3 : CompleteAt 260 3 := by decide +kernel
lemma complete_260_4 : CompleteAt 260 4 := by decide +kernel
lemma complete_case260 : ∀ e0, CompleteAt 260 e0 := by
  intro e0
  fin_cases e0
  · exact complete_260_0
  · exact complete_260_1
  · exact complete_260_2
  · exact complete_260_3
  · exact complete_260_4
#print axioms complete_case260
end Erdos184Work.PureSixLocalFilter1
