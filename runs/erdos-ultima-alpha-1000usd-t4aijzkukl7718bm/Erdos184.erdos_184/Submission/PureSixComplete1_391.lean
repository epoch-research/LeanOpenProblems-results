import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_391_0 : CompleteAt 391 0 := by decide +kernel
lemma complete_391_1 : CompleteAt 391 1 := by decide +kernel
lemma complete_391_2 : CompleteAt 391 2 := by decide +kernel
lemma complete_391_3 : CompleteAt 391 3 := by decide +kernel
lemma complete_391_4 : CompleteAt 391 4 := by decide +kernel
lemma complete_case391 : ∀ e0, CompleteAt 391 e0 := by
  intro e0
  fin_cases e0
  · exact complete_391_0
  · exact complete_391_1
  · exact complete_391_2
  · exact complete_391_3
  · exact complete_391_4
#print axioms complete_case391
end Erdos184Work.PureSixLocalFilter1
