import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_361_0 : CompleteAt 361 0 := by decide +kernel
lemma complete_361_1 : CompleteAt 361 1 := by decide +kernel
lemma complete_361_2 : CompleteAt 361 2 := by decide +kernel
lemma complete_361_3 : CompleteAt 361 3 := by decide +kernel
lemma complete_361_4 : CompleteAt 361 4 := by decide +kernel
lemma complete_case361 : ∀ e0, CompleteAt 361 e0 := by
  intro e0
  fin_cases e0
  · exact complete_361_0
  · exact complete_361_1
  · exact complete_361_2
  · exact complete_361_3
  · exact complete_361_4
#print axioms complete_case361
end Erdos184Work.PureSixLocalFilter1
