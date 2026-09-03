import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_116_0 : CompleteAt 116 0 := by decide +kernel
lemma complete_116_1 : CompleteAt 116 1 := by decide +kernel
lemma complete_116_2 : CompleteAt 116 2 := by decide +kernel
lemma complete_116_3 : CompleteAt 116 3 := by decide +kernel
lemma complete_116_4 : CompleteAt 116 4 := by decide +kernel
lemma complete_case116 : ∀ e0, CompleteAt 116 e0 := by
  intro e0
  fin_cases e0
  · exact complete_116_0
  · exact complete_116_1
  · exact complete_116_2
  · exact complete_116_3
  · exact complete_116_4
#print axioms complete_case116
end Erdos184Work.PureSixLocalFilter1
