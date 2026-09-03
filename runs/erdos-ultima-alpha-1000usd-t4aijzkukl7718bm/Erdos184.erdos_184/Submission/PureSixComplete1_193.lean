import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_193_0 : CompleteAt 193 0 := by decide +kernel
lemma complete_193_1 : CompleteAt 193 1 := by decide +kernel
lemma complete_193_2 : CompleteAt 193 2 := by decide +kernel
lemma complete_193_3 : CompleteAt 193 3 := by decide +kernel
lemma complete_193_4 : CompleteAt 193 4 := by decide +kernel
lemma complete_case193 : ∀ e0, CompleteAt 193 e0 := by
  intro e0
  fin_cases e0
  · exact complete_193_0
  · exact complete_193_1
  · exact complete_193_2
  · exact complete_193_3
  · exact complete_193_4
#print axioms complete_case193
end Erdos184Work.PureSixLocalFilter1
