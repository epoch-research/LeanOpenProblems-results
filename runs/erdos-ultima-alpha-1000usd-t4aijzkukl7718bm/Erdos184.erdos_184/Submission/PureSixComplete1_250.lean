import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_250_0 : CompleteAt 250 0 := by decide +kernel
lemma complete_250_1 : CompleteAt 250 1 := by decide +kernel
lemma complete_250_2 : CompleteAt 250 2 := by decide +kernel
lemma complete_250_3 : CompleteAt 250 3 := by decide +kernel
lemma complete_250_4 : CompleteAt 250 4 := by decide +kernel
lemma complete_case250 : ∀ e0, CompleteAt 250 e0 := by
  intro e0
  fin_cases e0
  · exact complete_250_0
  · exact complete_250_1
  · exact complete_250_2
  · exact complete_250_3
  · exact complete_250_4
#print axioms complete_case250
end Erdos184Work.PureSixLocalFilter1
