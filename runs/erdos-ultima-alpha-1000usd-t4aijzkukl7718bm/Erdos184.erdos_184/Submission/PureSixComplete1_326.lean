import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_326_0 : CompleteAt 326 0 := by decide +kernel
lemma complete_326_1 : CompleteAt 326 1 := by decide +kernel
lemma complete_326_2 : CompleteAt 326 2 := by decide +kernel
lemma complete_326_3 : CompleteAt 326 3 := by decide +kernel
lemma complete_326_4 : CompleteAt 326 4 := by decide +kernel
lemma complete_case326 : ∀ e0, CompleteAt 326 e0 := by
  intro e0
  fin_cases e0
  · exact complete_326_0
  · exact complete_326_1
  · exact complete_326_2
  · exact complete_326_3
  · exact complete_326_4
#print axioms complete_case326
end Erdos184Work.PureSixLocalFilter1
