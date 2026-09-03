import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_339_0 : CompleteAt 339 0 := by decide +kernel
lemma complete_339_1 : CompleteAt 339 1 := by decide +kernel
lemma complete_339_2 : CompleteAt 339 2 := by decide +kernel
lemma complete_339_3 : CompleteAt 339 3 := by decide +kernel
lemma complete_339_4 : CompleteAt 339 4 := by decide +kernel
lemma complete_case339 : ∀ e0, CompleteAt 339 e0 := by
  intro e0
  fin_cases e0
  · exact complete_339_0
  · exact complete_339_1
  · exact complete_339_2
  · exact complete_339_3
  · exact complete_339_4
#print axioms complete_case339
end Erdos184Work.PureSixLocalFilter1
