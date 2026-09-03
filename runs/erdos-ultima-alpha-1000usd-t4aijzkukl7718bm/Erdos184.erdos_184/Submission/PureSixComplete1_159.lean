import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_159_0 : CompleteAt 159 0 := by decide +kernel
lemma complete_159_1 : CompleteAt 159 1 := by decide +kernel
lemma complete_159_2 : CompleteAt 159 2 := by decide +kernel
lemma complete_159_3 : CompleteAt 159 3 := by decide +kernel
lemma complete_159_4 : CompleteAt 159 4 := by decide +kernel
lemma complete_case159 : ∀ e0, CompleteAt 159 e0 := by
  intro e0
  fin_cases e0
  · exact complete_159_0
  · exact complete_159_1
  · exact complete_159_2
  · exact complete_159_3
  · exact complete_159_4
#print axioms complete_case159
end Erdos184Work.PureSixLocalFilter1
