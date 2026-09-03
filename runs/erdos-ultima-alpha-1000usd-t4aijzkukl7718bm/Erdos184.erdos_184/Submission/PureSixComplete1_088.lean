import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_88_0 : CompleteAt 88 0 := by decide +kernel
lemma complete_88_1 : CompleteAt 88 1 := by decide +kernel
lemma complete_88_2 : CompleteAt 88 2 := by decide +kernel
lemma complete_88_3 : CompleteAt 88 3 := by decide +kernel
lemma complete_88_4 : CompleteAt 88 4 := by decide +kernel
lemma complete_case88 : ∀ e0, CompleteAt 88 e0 := by
  intro e0
  fin_cases e0
  · exact complete_88_0
  · exact complete_88_1
  · exact complete_88_2
  · exact complete_88_3
  · exact complete_88_4
#print axioms complete_case88
end Erdos184Work.PureSixLocalFilter1
