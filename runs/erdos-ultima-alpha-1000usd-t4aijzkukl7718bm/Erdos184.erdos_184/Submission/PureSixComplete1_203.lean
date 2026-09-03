import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_203_0 : CompleteAt 203 0 := by decide +kernel
lemma complete_203_1 : CompleteAt 203 1 := by decide +kernel
lemma complete_203_2 : CompleteAt 203 2 := by decide +kernel
lemma complete_203_3 : CompleteAt 203 3 := by decide +kernel
lemma complete_203_4 : CompleteAt 203 4 := by decide +kernel
lemma complete_case203 : ∀ e0, CompleteAt 203 e0 := by
  intro e0
  fin_cases e0
  · exact complete_203_0
  · exact complete_203_1
  · exact complete_203_2
  · exact complete_203_3
  · exact complete_203_4
#print axioms complete_case203
end Erdos184Work.PureSixLocalFilter1
