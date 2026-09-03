import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_234_0 : CompleteAt 234 0 := by decide +kernel
lemma complete_234_1 : CompleteAt 234 1 := by decide +kernel
lemma complete_234_2 : CompleteAt 234 2 := by decide +kernel
lemma complete_234_3 : CompleteAt 234 3 := by decide +kernel
lemma complete_234_4 : CompleteAt 234 4 := by decide +kernel
lemma complete_case234 : ∀ e0, CompleteAt 234 e0 := by
  intro e0
  fin_cases e0
  · exact complete_234_0
  · exact complete_234_1
  · exact complete_234_2
  · exact complete_234_3
  · exact complete_234_4
#print axioms complete_case234
end Erdos184Work.PureSixLocalFilter1
