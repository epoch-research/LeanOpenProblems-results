import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_349_0 : CompleteAt 349 0 := by decide +kernel
lemma complete_349_1 : CompleteAt 349 1 := by decide +kernel
lemma complete_349_2 : CompleteAt 349 2 := by decide +kernel
lemma complete_349_3 : CompleteAt 349 3 := by decide +kernel
lemma complete_349_4 : CompleteAt 349 4 := by decide +kernel
lemma complete_case349 : ∀ e0, CompleteAt 349 e0 := by
  intro e0
  fin_cases e0
  · exact complete_349_0
  · exact complete_349_1
  · exact complete_349_2
  · exact complete_349_3
  · exact complete_349_4
#print axioms complete_case349
end Erdos184Work.PureSixLocalFilter1
