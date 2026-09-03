import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_336_0 : CompleteAt 336 0 := by decide +kernel
lemma complete_336_1 : CompleteAt 336 1 := by decide +kernel
lemma complete_336_2 : CompleteAt 336 2 := by decide +kernel
lemma complete_336_3 : CompleteAt 336 3 := by decide +kernel
lemma complete_336_4 : CompleteAt 336 4 := by decide +kernel
lemma complete_case336 : ∀ e0, CompleteAt 336 e0 := by
  intro e0
  fin_cases e0
  · exact complete_336_0
  · exact complete_336_1
  · exact complete_336_2
  · exact complete_336_3
  · exact complete_336_4
#print axioms complete_case336
end Erdos184Work.PureSixLocalFilter1
