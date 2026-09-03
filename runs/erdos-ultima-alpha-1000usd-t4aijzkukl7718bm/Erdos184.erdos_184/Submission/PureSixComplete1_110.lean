import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_110_0 : CompleteAt 110 0 := by decide +kernel
lemma complete_110_1 : CompleteAt 110 1 := by decide +kernel
lemma complete_110_2 : CompleteAt 110 2 := by decide +kernel
lemma complete_110_3 : CompleteAt 110 3 := by decide +kernel
lemma complete_110_4 : CompleteAt 110 4 := by decide +kernel
lemma complete_case110 : ∀ e0, CompleteAt 110 e0 := by
  intro e0
  fin_cases e0
  · exact complete_110_0
  · exact complete_110_1
  · exact complete_110_2
  · exact complete_110_3
  · exact complete_110_4
#print axioms complete_case110
end Erdos184Work.PureSixLocalFilter1
