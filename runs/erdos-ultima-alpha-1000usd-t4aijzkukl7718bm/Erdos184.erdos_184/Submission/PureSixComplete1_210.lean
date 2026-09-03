import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_210_0 : CompleteAt 210 0 := by decide +kernel
lemma complete_210_1 : CompleteAt 210 1 := by decide +kernel
lemma complete_210_2 : CompleteAt 210 2 := by decide +kernel
lemma complete_210_3 : CompleteAt 210 3 := by decide +kernel
lemma complete_210_4 : CompleteAt 210 4 := by decide +kernel
lemma complete_case210 : ∀ e0, CompleteAt 210 e0 := by
  intro e0
  fin_cases e0
  · exact complete_210_0
  · exact complete_210_1
  · exact complete_210_2
  · exact complete_210_3
  · exact complete_210_4
#print axioms complete_case210
end Erdos184Work.PureSixLocalFilter1
