import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_162_0 : CompleteAt 162 0 := by decide +kernel
lemma complete_162_1 : CompleteAt 162 1 := by decide +kernel
lemma complete_162_2 : CompleteAt 162 2 := by decide +kernel
lemma complete_162_3 : CompleteAt 162 3 := by decide +kernel
lemma complete_162_4 : CompleteAt 162 4 := by decide +kernel
lemma complete_case162 : ∀ e0, CompleteAt 162 e0 := by
  intro e0
  fin_cases e0
  · exact complete_162_0
  · exact complete_162_1
  · exact complete_162_2
  · exact complete_162_3
  · exact complete_162_4
#print axioms complete_case162
end Erdos184Work.PureSixLocalFilter1
