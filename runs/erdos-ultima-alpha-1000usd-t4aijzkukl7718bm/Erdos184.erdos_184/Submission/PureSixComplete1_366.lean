import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_366_0 : CompleteAt 366 0 := by decide +kernel
lemma complete_366_1 : CompleteAt 366 1 := by decide +kernel
lemma complete_366_2 : CompleteAt 366 2 := by decide +kernel
lemma complete_366_3 : CompleteAt 366 3 := by decide +kernel
lemma complete_366_4 : CompleteAt 366 4 := by decide +kernel
lemma complete_case366 : ∀ e0, CompleteAt 366 e0 := by
  intro e0
  fin_cases e0
  · exact complete_366_0
  · exact complete_366_1
  · exact complete_366_2
  · exact complete_366_3
  · exact complete_366_4
#print axioms complete_case366
end Erdos184Work.PureSixLocalFilter1
