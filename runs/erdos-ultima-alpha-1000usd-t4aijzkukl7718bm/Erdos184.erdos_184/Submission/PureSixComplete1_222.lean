import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_222_0 : CompleteAt 222 0 := by decide +kernel
lemma complete_222_1 : CompleteAt 222 1 := by decide +kernel
lemma complete_222_2 : CompleteAt 222 2 := by decide +kernel
lemma complete_222_3 : CompleteAt 222 3 := by decide +kernel
lemma complete_222_4 : CompleteAt 222 4 := by decide +kernel
lemma complete_case222 : ∀ e0, CompleteAt 222 e0 := by
  intro e0
  fin_cases e0
  · exact complete_222_0
  · exact complete_222_1
  · exact complete_222_2
  · exact complete_222_3
  · exact complete_222_4
#print axioms complete_case222
end Erdos184Work.PureSixLocalFilter1
